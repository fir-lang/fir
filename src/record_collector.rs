use crate::ast;
use crate::collections::Set;

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

pub fn collect_records(pgm: &[ast::L<ast::TopDecl>]) -> (Set<RecordShape>, Set<VariantShape>) {
    let mut records: Set<RecordShape> = Default::default();
    let mut variants: Set<VariantShape> = Default::default();

    for decl in pgm {
        match &decl.node {
            ast::TopDecl::Type(ty_decl) => {
                visit_ty_decl(&ty_decl.node, &mut records, &mut variants)
            }
            ast::TopDecl::Fun(fun_decl) => {
                visit_fun_decl(&fun_decl.node, &mut records, &mut variants)
            }
            ast::TopDecl::Trait(trait_decl) => {
                visit_trait_decl(&trait_decl.node, &mut records, &mut variants)
            }
            ast::TopDecl::Impl(impl_decl) => {
                visit_impl_decl(&impl_decl.node, &mut records, &mut variants)
            }
            ast::TopDecl::Import(_) => panic!("Import declaration in record collector"),
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
        for stmt in &body.node {
            visit_stmt(&stmt.node, records, variants);
        }
    }
}

fn visit_trait_decl(
    trait_decl: &ast::TraitDecl,
    records: &mut Set<RecordShape>,
    variants: &mut Set<VariantShape>,
) {
    for ty in &trait_decl.ty.node.1 {
        visit_ty(&ty.node, records, variants);
    }
    for item in &trait_decl.items {
        visit_trait_decl_item(&item.node, records, variants);
    }
}

fn visit_trait_decl_item(
    item: &ast::TraitDeclItem,
    records: &mut Set<RecordShape>,
    variants: &mut Set<VariantShape>,
) {
    match item {
        ast::TraitDeclItem::AssocTy(_) => {}
        ast::TraitDeclItem::Fun(fun_decl) => visit_fun_decl(fun_decl, records, variants),
    }
}

fn visit_impl_decl(
    impl_decl: &ast::ImplDecl,
    records: &mut Set<RecordShape>,
    variants: &mut Set<VariantShape>,
) {
    for context_ty in &impl_decl.context {
        for bound in &context_ty.node.1 {
            visit_ty(&bound.node, records, variants);
        }
    }

    for item in &impl_decl.items {
        visit_impl_decl_item(&item.node, records, variants);
    }
}

fn visit_impl_decl_item(
    item: &ast::ImplDeclItem,
    records: &mut Set<RecordShape>,
    variants: &mut Set<VariantShape>,
) {
    match item {
        ast::ImplDeclItem::AssocTy(ast::AssocTyDecl { name: _, ty }) => {
            visit_ty(&ty.node, records, variants)
        }
        ast::ImplDeclItem::Fun(fun_decl) => visit_fun_decl(fun_decl, records, variants),
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
            .for_each(|arg| visit_ty(&arg.node.1.node, records, variants)),

        ast::Type::Record { fields, extension } => {
            assert_eq!(extension, &None);
            records.insert(RecordShape::from_named_things(fields));
        }

        ast::Type::Variant { .. } => todo!(),

        ast::Type::Fn(ast::FnType { args, ret }) => {
            for arg in args {
                visit_ty(&arg.node, records, variants);
            }
            if let Some(ret) = ret {
                visit_ty(&ret.node, records, variants);
            }
        }
    }
}

fn visit_stmt(stmt: &ast::Stmt, records: &mut Set<RecordShape>, variants: &mut Set<VariantShape>) {
    match stmt {
        ast::Stmt::Break | ast::Stmt::Continue => {}

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
            var: _,
            ty,
            expr,
            expr_ty: _,
            body,
        }) => {
            if let Some(ty) = ty {
                visit_ty(ty, records, variants);
            }
            visit_expr(&expr.node, records, variants);
            for stmt in body {
                visit_stmt(&stmt.node, records, variants);
            }
        }

        ast::Stmt::While(ast::WhileStmt { cond, body }) => {
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

        ast::Pat::Constr(ast::ConstrPattern {
            constr: _,
            fields,
            ty_args: _,
        }) => {
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
        ast::Expr::Var(_)
        | ast::Expr::Constr(_)
        | ast::Expr::Int(_)
        | ast::Expr::Self_
        | ast::Expr::Char(_) => {}

        ast::Expr::String(parts) => {
            for part in parts {
                match part {
                    crate::interpolation::StringPart::Str(_) => {}
                    crate::interpolation::StringPart::Expr(expr) => {
                        visit_expr(&expr.node, records, variants)
                    }
                }
            }
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field: _ }) => {
            visit_expr(&object.node, records, variants);
        }

        ast::Expr::MethodSelect(ast::MethodSelectExpr {
            object, method: _, ..
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

        ast::Expr::Range(ast::RangeExpr {
            from,
            to,
            inclusive: _,
        }) => {
            visit_expr(&from.node, records, variants);
            visit_expr(&to.node, records, variants);
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
    }
}
