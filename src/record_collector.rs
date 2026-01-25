use crate::ast::Id;
use crate::collections::*;
use crate::mono_ast as mono;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RecordType {
    pub(crate) fields: OrdMap<Id, mono::Type>,
}

impl RecordType {
    pub fn unit() -> RecordType {
        RecordType {
            fields: Default::default(),
        }
    }
}

pub fn collect_records(pgm: &mono::MonoPgm) -> HashSet<RecordType> {
    let mut records: HashSet<RecordType> = Default::default();

    for ty_map in pgm.funs.values() {
        for (tys, fun) in ty_map {
            for ty in tys {
                visit_ty(ty, &mut records);
            }
            visit_fun_decl(fun, &mut records);
        }
    }

    for method_map in pgm.associated.values() {
        for ty_map in method_map.values() {
            for (tys, fun) in ty_map {
                for ty in tys {
                    visit_ty(ty, &mut records);
                }
                visit_fun_decl(fun, &mut records);
            }
        }
    }

    for ty in pgm.ty.values() {
        for (tys, ty) in ty {
            for ty in tys {
                visit_ty(ty, &mut records);
            }
            visit_ty_decl(ty, &mut records);
        }
    }

    records
}

fn visit_ty_decl(ty_decl: &mono::TypeDecl, records: &mut HashSet<RecordType>) {
    match &ty_decl.rhs {
        None => {}

        Some(mono::TypeDeclRhs::Sum(cons)) => {
            for con in cons {
                visit_fields(&con.fields, records);
            }
        }

        Some(mono::TypeDeclRhs::Product(fields)) => {
            visit_fields(fields, records);
        }
    }
}

fn visit_fun_decl(fun_decl: &mono::FunDecl, records: &mut HashSet<RecordType>) {
    visit_fun_sig(&fun_decl.sig, records);

    if let Some(body) = &fun_decl.body {
        for stmt in body {
            visit_stmt(&stmt.node, records);
        }
    }
}

fn visit_fun_sig(sig: &mono::FunSig, records: &mut HashSet<RecordType>) {
    for (_param_name, param_ty) in &sig.params {
        visit_ty(&param_ty.node, records);
    }

    match &sig.return_ty {
        Some(ty) => {
            visit_ty(&ty.node, records);
        }
        None => {
            visit_ty(&mono::Type::unit(), records);
        }
    }

    if let Some(ty) = &sig.exceptions {
        visit_ty(&ty.node, records);
    }
}

fn visit_fields(fields: &mono::ConFields, records: &mut HashSet<RecordType>) {
    match fields {
        mono::ConFields::Empty => {}

        mono::ConFields::Named(named_fields) => named_fields
            .iter()
            .for_each(|(_name, ty)| visit_ty(ty, records)),

        mono::ConFields::Unnamed(fields) => fields.iter().for_each(|ty| visit_ty(ty, records)),
    }
}

fn visit_ty(ty: &mono::Type, records: &mut HashSet<RecordType>) {
    match ty {
        mono::Type::Named(mono::NamedType { name: _, args }) => {
            args.iter().for_each(|arg| visit_ty(arg, records))
        }

        mono::Type::Record { fields } => {
            records.insert(RecordType {
                fields: fields.clone(),
            });
        }

        mono::Type::Variant { alts } => {
            for mono::NamedType { name: _, args } in alts.values() {
                args.iter().for_each(|arg| visit_ty(arg, records))
            }
        }

        mono::Type::Fn(mono::FnType { args, ret, exn }) => {
            match args {
                mono::FunArgs::Positional(args) => {
                    args.iter().for_each(|ty| visit_ty(ty, records));
                }
                mono::FunArgs::Named(args) => {
                    args.values().for_each(|ty| visit_ty(ty, records));
                }
            }
            visit_ty(ret, records);
            visit_ty(exn, records);
        }

        mono::Type::Never => {}
    }
}

fn visit_stmt(stmt: &mono::Stmt, records: &mut HashSet<RecordType>) {
    match stmt {
        mono::Stmt::Break { .. } | mono::Stmt::Continue { .. } => {}

        mono::Stmt::Let(mono::LetStmt { lhs, rhs }) => {
            visit_pat(&lhs.node, records);
            visit_expr(&rhs.node, records);
        }

        mono::Stmt::Assign(mono::AssignStmt { lhs, rhs }) => {
            visit_expr(&lhs.node, records);
            visit_expr(&rhs.node, records);
        }

        mono::Stmt::Expr(expr) => visit_expr(expr, records),

        mono::Stmt::While(mono::WhileStmt {
            label: _,
            cond,
            body,
        }) => {
            visit_expr(&cond.node, records);
            for stmt in body {
                visit_stmt(&stmt.node, records);
            }
        }
    }
}

fn visit_pat(pat: &mono::Pat, records: &mut HashSet<RecordType>) {
    match pat {
        mono::Pat::Var(_) | mono::Pat::Ignore | mono::Pat::Str(_) | mono::Pat::Char(_) => {}

        mono::Pat::Con(mono::ConPat { con: _, fields }) => {
            for field in fields {
                visit_pat(&field.node.node, records);
            }
        }

        mono::Pat::Record(mono::RecordPat { fields, ty }) => {
            records.insert(RecordType { fields: ty.clone() });
            for field in fields {
                visit_pat(&field.node.node, records);
            }
        }

        mono::Pat::Or(pat1, pat2) => {
            visit_pat(&pat1.node, records);
            visit_pat(&pat2.node, records);
        }

        mono::Pat::Variant(mono::VariantPat { pat, ty }) => {
            visit_ty(&mono::Type::Variant { alts: ty.clone() }, records);
            visit_pat(&pat.node, records);
        }
    }
}

fn visit_expr(expr: &mono::Expr, records: &mut HashSet<RecordType>) {
    match expr {
        mono::Expr::LocalVar(_, _)
        | mono::Expr::TopVar(_)
        | mono::Expr::ConSel(_)
        | mono::Expr::AssocFnSel(_)
        | mono::Expr::Int(_)
        | mono::Expr::Char(_)
        | mono::Expr::Str(_) => {}

        mono::Expr::FieldSel(mono::FieldSelExpr {
            object,
            field: _,
            ty,
        }) => {
            visit_ty(ty, records);
            visit_expr(&object.node, records);
        }

        mono::Expr::Call(mono::CallExpr { fun, args, ty }) => {
            visit_ty(ty, records);
            visit_expr(&fun.node, records);
            for arg in args {
                visit_expr(&arg.expr.node, records);
            }
        }

        mono::Expr::BoolOr(left, right) | mono::Expr::BoolAnd(left, right) => {
            visit_expr(&left.node, records);
            visit_expr(&right.node, records);
        }

        mono::Expr::Return(expr, ty) => {
            visit_ty(ty, records);
            visit_expr(&expr.node, records)
        }

        mono::Expr::Match(mono::MatchExpr {
            scrutinee,
            alts,
            ty,
        }) => {
            visit_ty(ty, records);
            visit_expr(&scrutinee.node, records);
            for alt in alts {
                visit_pat(&alt.pat.node, records);
                if let Some(guard) = &alt.guard {
                    visit_expr(&guard.node, records);
                }
                for stmt in &alt.rhs {
                    visit_stmt(&stmt.node, records);
                }
            }
        }

        mono::Expr::If(mono::IfExpr {
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

        mono::Expr::Fn(mono::FnExpr { sig, body }) => {
            visit_fun_sig(sig, records);
            for stmt in body {
                visit_stmt(&stmt.node, records);
            }
        }

        mono::Expr::Is(mono::IsExpr { expr, pat }) => {
            visit_expr(&expr.node, records);
            visit_pat(&pat.node, records);
        }

        mono::Expr::Do(stmts, ty) => {
            visit_ty(ty, records);
            for stmt in stmts {
                visit_stmt(&stmt.node, records);
            }
        }

        mono::Expr::Record(mono::RecordExpr { fields, ty }) => {
            records.insert(RecordType { fields: ty.clone() });
            for (_field_name, field_expr) in fields {
                visit_expr(&field_expr.node, records);
            }
        }

        mono::Expr::Variant(mono::VariantExpr { expr, ty }) => {
            visit_ty(&mono::Type::Variant { alts: ty.clone() }, records);
            visit_expr(&expr.node, records);
        }
    }
}
