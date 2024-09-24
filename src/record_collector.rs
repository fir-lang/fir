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

pub fn collect_records(pgm: &[ast::L<ast::TopDecl>]) -> Set<RecordShape> {
    let mut records: Set<RecordShape> = Default::default();

    for decl in pgm {
        match &decl.node {
            ast::TopDecl::Type(ty_decl) => visit_ty_decl(&ty_decl.node, &mut records),
            ast::TopDecl::Fun(fun_decl) => visit_fun_decl(&fun_decl.node, &mut records),
            ast::TopDecl::Trait(trait_decl) => visit_trait_decl(&trait_decl.node, &mut records),
            ast::TopDecl::Impl(impl_decl) => visit_impl_decl(&impl_decl.node, &mut records),
            ast::TopDecl::Import(_) => panic!("Import declaration in record collector"),
        }
    }

    records
}

fn visit_ty_decl(ty_decl: &ast::TypeDecl, records: &mut Set<RecordShape>) {
    match &ty_decl.rhs {
        None => {}

        Some(ast::TypeDeclRhs::Sum(constrs)) => {
            for constr in constrs {
                visit_fields(&constr.fields, records);
            }
        }

        Some(ast::TypeDeclRhs::Product(fields)) => {
            visit_fields(fields, records);
        }
    }
}

fn visit_fun_decl(fun_decl: &ast::FunDecl, records: &mut Set<RecordShape>) {
    visit_fun_sig(&fun_decl.sig, records);

    if let Some(body) = &fun_decl.body {
        for stmt in &body.node {
            visit_stmt(&stmt.node, records);
        }
    }
}

fn visit_trait_decl(trait_decl: &ast::TraitDecl, records: &mut Set<RecordShape>) {
    for ty in &trait_decl.ty.node.1 {
        visit_ty(&ty.node, records);
    }
    for item in &trait_decl.items {
        visit_trait_decl_item(&item.node, records);
    }
}

fn visit_trait_decl_item(item: &ast::TraitDeclItem, records: &mut Set<RecordShape>) {
    match item {
        ast::TraitDeclItem::AssocTy(_) => {}
        ast::TraitDeclItem::Fun(fun_decl) => visit_fun_decl(fun_decl, records),
    }
}

fn visit_impl_decl(impl_decl: &ast::ImplDecl, records: &mut Set<RecordShape>) {
    for context_ty in &impl_decl.context {
        for bound in &context_ty.node.1 {
            visit_ty(&bound.node, records);
        }
    }

    for item in &impl_decl.items {
        visit_impl_decl_item(&item.node, records);
    }
}

fn visit_impl_decl_item(item: &ast::ImplDeclItem, records: &mut Set<RecordShape>) {
    match item {
        ast::ImplDeclItem::AssocTy(ast::AssocTyDecl { name: _, ty }) => visit_ty(&ty.node, records),
        ast::ImplDeclItem::Fun(fun_decl) => visit_fun_decl(fun_decl, records),
    }
}

fn visit_fun_sig(sig: &ast::FunSig, records: &mut Set<RecordShape>) {
    for (_param_name, param_ty) in &sig.params {
        visit_ty(&param_ty.node, records);
    }

    if let Some(return_ty) = &sig.return_ty {
        visit_ty(&return_ty.node, records);
    }
}

fn visit_fields(fields: &ast::ConstructorFields, records: &mut Set<RecordShape>) {
    match fields {
        ast::ConstructorFields::Empty => {}

        ast::ConstructorFields::Named(named_fields) => named_fields
            .iter()
            .for_each(|(_name, ty)| visit_ty(ty, records)),

        ast::ConstructorFields::Unnamed(fields) => {
            fields.iter().for_each(|ty| visit_ty(ty, records))
        }
    }
}

fn visit_ty(ty: &ast::Type, records: &mut Set<RecordShape>) {
    match ty {
        ast::Type::Named(ast::NamedType { name: _, args }) => args
            .iter()
            .for_each(|arg| visit_ty(&arg.node.1.node, records)),

        ast::Type::Record(fields) => {
            records.insert(RecordShape::from_named_things(fields));
        }
    }
}

fn visit_stmt(stmt: &ast::Stmt, records: &mut Set<RecordShape>) {
    match stmt {
        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => {
            visit_pat(&lhs.node, records);
            if let Some(ty) = ty {
                visit_ty(&ty.node, records);
            }
            visit_expr(&rhs.node, records);
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op: _ }) => {
            visit_expr(&lhs.node, records);
            visit_expr(&rhs.node, records);
        }

        ast::Stmt::Expr(expr) => visit_expr(&expr.node, records),

        ast::Stmt::For(ast::ForStmt {
            var: _,
            ty,
            expr,
            body,
        }) => {
            if let Some(ty) = ty {
                visit_ty(ty, records);
            }
            visit_expr(&expr.node, records);
            for stmt in body {
                visit_stmt(&stmt.node, records);
            }
        }

        ast::Stmt::While(ast::WhileStmt { cond, body }) => {
            visit_expr(&cond.node, records);
            for stmt in body {
                visit_stmt(&stmt.node, records);
            }
        }
    }
}

fn visit_pat(pat: &ast::Pat, records: &mut Set<RecordShape>) {
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
                visit_pat(&field.node.node, records);
            }
        }

        ast::Pat::Record(fields) => {
            for field in fields {
                visit_pat(&field.node.node, records);
            }
            records.insert(RecordShape::from_named_things(fields));
        }

        ast::Pat::Or(pat1, pat2) => {
            visit_pat(&pat1.node, records);
            visit_pat(&pat2.node, records);
        }
    }
}

fn visit_expr(expr: &ast::Expr, records: &mut Set<RecordShape>) {
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
                    crate::interpolation::StringPart::Expr(expr) => visit_expr(&expr.node, records),
                }
            }
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field: _ }) => {
            visit_expr(&object.node, records);
        }

        ast::Expr::MethodSelect(ast::MethodSelectExpr {
            object, method: _, ..
        }) => {
            visit_expr(&object.node, records);
        }

        ast::Expr::ConstrSelect(_) | ast::Expr::AssocFnSelect(_) => {}

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            visit_expr(&fun.node, records);
            for arg in args {
                visit_expr(&arg.expr.node, records);
            }
        }

        ast::Expr::Range(ast::RangeExpr {
            from,
            to,
            inclusive: _,
        }) => {
            visit_expr(&from.node, records);
            visit_expr(&to.node, records);
        }

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op: _ }) => {
            visit_expr(&left.node, records);
            visit_expr(&right.node, records);
        }

        ast::Expr::UnOp(ast::UnOpExpr { op: _, expr }) => {
            visit_expr(&expr.node, records);
        }

        ast::Expr::Record(fields) => {
            for field in fields {
                visit_expr(&field.node.node, records);
            }
            records.insert(RecordShape::from_named_things(fields));
        }

        ast::Expr::Return(expr) => visit_expr(&expr.node, records),

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            visit_expr(&scrutinee.node, records);
            for alt in alts {
                visit_pat(&alt.pattern.node, records);
                if let Some(guard) = &alt.guard {
                    visit_expr(&guard.node, records);
                }
                for stmt in &alt.rhs {
                    visit_stmt(&stmt.node, records);
                }
            }
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            for (expr, stmts) in branches {
                visit_expr(&expr.node, records);
                for stmt in stmts {
                    visit_stmt(&stmt.node, records);
                }
            }
            if let Some(else_branch) = else_branch {
                for stmt in else_branch {
                    visit_stmt(&stmt.node, records);
                }
            }
        }

        ast::Expr::As(ast::AsExpr {
            expr,
            expr_ty: _,
            target_ty: _,
        }) => visit_expr(&expr.node, records),
    }
}
