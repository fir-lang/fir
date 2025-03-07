use crate::collections::Set;
use crate::mono_ast as ast;

use smol_str::SmolStr;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RecordShape {
    UnnamedFields {
        arity: u32,
    },

    NamedFields {
        // Sorted.
        fields: Vec<SmolStr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VariantShape {
    pub con_name: SmolStr,
    pub payload: RecordShape,
}

impl RecordShape {
    pub fn from_named_things<T>(things: &[ast::Named<T>]) -> RecordShape {
        // All or none of the fields should be named.
        if things.is_empty() {
            return RecordShape::UnnamedFields { arity: 0 };
        }

        if things[0].name.is_some() {
            let mut names: Set<SmolStr> = Default::default();
            for thing in things {
                let new = names.insert(thing.name.clone().unwrap());
                assert!(new);
            }
            let mut fields: Vec<SmolStr> = names.into_iter().collect();
            fields.sort();
            RecordShape::NamedFields { fields }
        } else {
            RecordShape::UnnamedFields {
                arity: things.len() as u32,
            }
        }
    }
}

impl VariantShape {
    pub fn from_con_and_fields<T>(con: &SmolStr, fields: &[ast::Named<T>]) -> VariantShape {
        let record_shape = RecordShape::from_named_things(fields);
        VariantShape {
            con_name: con.clone(),
            payload: record_shape,
        }
    }
}

pub fn collect_records(pgm: &ast::MonoPgm) -> (Set<RecordShape>, Set<VariantShape>) {
    let mut records: Set<RecordShape> = Default::default();
    let mut variants: Set<VariantShape> = Default::default();

    for ty_map in pgm.funs.values() {
        for (tys, fun) in ty_map {
            for ty in tys {
                visit_ty(ty, &mut records, &mut variants);
            }
            visit_fun_decl(fun, &mut records, &mut variants);
        }
    }

    for method_map in pgm.associated.values() {
        for ty_map in method_map.values() {
            for (tys, fun) in ty_map {
                for ty in tys {
                    visit_ty(ty, &mut records, &mut variants);
                }
                visit_fun_decl(fun, &mut records, &mut variants);
            }
        }
    }

    for ty in pgm.ty.values() {
        for (tys, ty) in ty {
            for ty in tys {
                visit_ty(ty, &mut records, &mut variants);
            }
            visit_ty_decl(ty, &mut records, &mut variants);
        }
    }

    (records, variants)
}

fn visit_ty_decl(
    ty_decl: &ast::TypeDecl,
    records: &mut Set<RecordShape>,
    variants: &mut Set<VariantShape>,
) {
    match &ty_decl.rhs {
        None => {}

        Some(ast::TypeDeclRhs::Sum(constrs)) => {
            for constr in constrs {
                visit_fields(&constr.fields, records, variants);
            }
        }

        Some(ast::TypeDeclRhs::Product(fields)) => {
            visit_fields(fields, records, variants);
        }
    }
}

fn visit_fun_decl(
    fun_decl: &ast::FunDecl,
    records: &mut Set<RecordShape>,
    variants: &mut Set<VariantShape>,
) {
    visit_fun_sig(&fun_decl.sig, records, variants);

    if let Some(body) = &fun_decl.body {
        for stmt in body {
            visit_stmt(&stmt.node, records, variants);
        }
    }
}

fn visit_fun_sig(
    sig: &ast::FunSig,
    records: &mut Set<RecordShape>,
    variants: &mut Set<VariantShape>,
) {
    for (_param_name, param_ty) in &sig.params {
        visit_ty(&param_ty.node, records, variants);
    }

    if let Some(return_ty) = &sig.return_ty {
        visit_ty(&return_ty.node, records, variants);
    }
}

fn visit_fields(
    fields: &ast::ConstructorFields,
    records: &mut Set<RecordShape>,
    variants: &mut Set<VariantShape>,
) {
    match fields {
        ast::ConstructorFields::Empty => {}

        ast::ConstructorFields::Named(named_fields) => named_fields
            .iter()
            .for_each(|(_name, ty)| visit_ty(ty, records, variants)),

        ast::ConstructorFields::Unnamed(fields) => {
            fields.iter().for_each(|ty| visit_ty(ty, records, variants))
        }
    }
}

fn visit_ty(ty: &ast::Type, records: &mut Set<RecordShape>, variants: &mut Set<VariantShape>) {
    match ty {
        ast::Type::Named(ast::NamedType { name: _, args }) => args
            .iter()
            .for_each(|arg| visit_ty(&arg.node, records, variants)),

        ast::Type::Record { fields } => {
            records.insert(RecordShape::from_named_things(fields));
        }

        ast::Type::Variant { alts } => {
            for ast::VariantAlt { con, fields } in alts {
                variants.insert(VariantShape::from_con_and_fields(con, fields));
            }
        }

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => {
            for arg in args {
                visit_ty(&arg.node, records, variants);
            }
            if let Some(ret) = ret {
                visit_ty(&ret.node, records, variants);
            }
            if let Some(exn) = exceptions {
                visit_ty(&exn.node, records, variants);
            }
        }
    }
}

fn visit_stmt(stmt: &ast::Stmt, records: &mut Set<RecordShape>, variants: &mut Set<VariantShape>) {
    match stmt {
        ast::Stmt::Break { .. } | ast::Stmt::Continue { .. } => {}

        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => {
            visit_pat(&lhs.node, records, variants);
            if let Some(ty) = ty {
                visit_ty(&ty.node, records, variants);
            }
            visit_expr(&rhs.node, records, variants);
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op: _ }) => {
            visit_expr(&lhs.node, records, variants);
            visit_expr(&rhs.node, records, variants);
        }

        ast::Stmt::Expr(expr) => visit_expr(&expr.node, records, variants),

        ast::Stmt::For(ast::ForStmt {
            label: _,
            pat,
            expr,
            body,
        }) => {
            visit_pat(&pat.node, records, variants);
            visit_expr(&expr.node, records, variants);
            for stmt in body {
                visit_stmt(&stmt.node, records, variants);
            }
        }

        ast::Stmt::While(ast::WhileStmt {
            label: _,
            cond,
            body,
        }) => {
            visit_expr(&cond.node, records, variants);
            for stmt in body {
                visit_stmt(&stmt.node, records, variants);
            }
        }

        ast::Stmt::WhileLet(ast::WhileLetStmt {
            label: _,
            pat,
            cond,
            body,
        }) => {
            visit_pat(&pat.node, records, variants);
            visit_expr(&cond.node, records, variants);
            for stmt in body {
                visit_stmt(&stmt.node, records, variants);
            }
        }
    }
}

fn visit_pat(pat: &ast::Pat, records: &mut Set<RecordShape>, variants: &mut Set<VariantShape>) {
    match pat {
        ast::Pat::Var(_)
        | ast::Pat::Ignore
        | ast::Pat::Str(_)
        | ast::Pat::StrPfx(_, _)
        | ast::Pat::Char(_) => {}

        ast::Pat::Constr(ast::ConstrPattern { constr: _, fields }) => {
            for field in fields {
                visit_pat(&field.node.node, records, variants);
            }
        }

        ast::Pat::Record(fields) => {
            for field in fields {
                visit_pat(&field.node.node, records, variants);
            }
            records.insert(RecordShape::from_named_things(fields));
        }

        ast::Pat::Variant(ast::VariantPattern { constr, fields }) => {
            variants.insert(VariantShape::from_con_and_fields(constr, fields));
        }

        ast::Pat::Or(pat1, pat2) => {
            visit_pat(&pat1.node, records, variants);
            visit_pat(&pat2.node, records, variants);
        }
    }
}

fn visit_expr(expr: &ast::Expr, records: &mut Set<RecordShape>, variants: &mut Set<VariantShape>) {
    match expr {
        ast::Expr::LocalVar(_)
        | ast::Expr::TopVar(_)
        | ast::Expr::Constr(_)
        | ast::Expr::Int(_)
        | ast::Expr::Self_
        | ast::Expr::Char(_) => {}

        ast::Expr::String(parts) => {
            for part in parts {
                match part {
                    ast::StringPart::Str(_) => {}
                    ast::StringPart::Expr(expr) => visit_expr(&expr.node, records, variants),
                }
            }
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field: _ }) => {
            visit_expr(&object.node, records, variants);
        }

        ast::Expr::MethodSelect(ast::MethodSelectExpr {
            object,
            method_ty_id: _,
            method_id: _,
            ty_args: _,
        }) => {
            visit_expr(&object.node, records, variants);
        }

        ast::Expr::ConstrSelect(_) | ast::Expr::AssocFnSelect(_) => {}

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            visit_expr(&fun.node, records, variants);
            for arg in args {
                visit_expr(&arg.expr.node, records, variants);
            }
        }

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op: _ }) => {
            visit_expr(&left.node, records, variants);
            visit_expr(&right.node, records, variants);
        }

        ast::Expr::UnOp(ast::UnOpExpr { op: _, expr }) => {
            visit_expr(&expr.node, records, variants);
        }

        ast::Expr::Record(fields) => {
            for field in fields {
                visit_expr(&field.node.node, records, variants);
            }
            records.insert(RecordShape::from_named_things(fields));
        }

        ast::Expr::Variant(ast::VariantExpr { id, args }) => {
            variants.insert(VariantShape::from_con_and_fields(id, args));
        }

        ast::Expr::Return(expr) => visit_expr(&expr.node, records, variants),

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            visit_expr(&scrutinee.node, records, variants);
            for alt in alts {
                visit_pat(&alt.pattern.node, records, variants);
                if let Some(guard) = &alt.guard {
                    visit_expr(&guard.node, records, variants);
                }
                for stmt in &alt.rhs {
                    visit_stmt(&stmt.node, records, variants);
                }
            }
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            for (expr, stmts) in branches {
                visit_expr(&expr.node, records, variants);
                for stmt in stmts {
                    visit_stmt(&stmt.node, records, variants);
                }
            }
            if let Some(else_branch) = else_branch {
                for stmt in else_branch {
                    visit_stmt(&stmt.node, records, variants);
                }
            }
        }

        ast::Expr::Fn(ast::FnExpr { sig, body, idx: _ }) => {
            visit_fun_sig(sig, records, variants);
            for stmt in body {
                visit_stmt(&stmt.node, records, variants);
            }
        }
    }
}
