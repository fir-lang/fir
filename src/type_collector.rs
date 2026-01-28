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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct VariantType {
    pub(crate) alts: OrdMap<Id, mono::NamedType>,
}

pub fn collect_anonymous_types(pgm: &mono::MonoPgm) -> (HashSet<RecordType>, HashSet<VariantType>) {
    let mut records: HashSet<RecordType> = Default::default();
    let mut variants: HashSet<VariantType> = Default::default();

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
    ty_decl: &mono::TypeDecl,
    records: &mut HashSet<RecordType>,
    variants: &mut HashSet<VariantType>,
) {
    match &ty_decl.rhs {
        None => {}

        Some(mono::TypeDeclRhs::Sum(cons)) => {
            for con in cons {
                visit_fields(&con.fields, records, variants);
            }
        }

        Some(mono::TypeDeclRhs::Product(fields)) => {
            visit_fields(fields, records, variants);
        }
    }
}

fn visit_fun_decl(
    fun_decl: &mono::FunDecl,
    records: &mut HashSet<RecordType>,
    variants: &mut HashSet<VariantType>,
) {
    visit_fun_sig(&fun_decl.sig, records, variants);

    if let Some(body) = &fun_decl.body {
        for stmt in body {
            visit_stmt(&stmt.node, records, variants);
        }
    }
}

fn visit_fun_sig(
    sig: &mono::FunSig,
    records: &mut HashSet<RecordType>,
    variants: &mut HashSet<VariantType>,
) {
    for (_param_name, param_ty) in &sig.params {
        visit_ty(&param_ty.node, records, variants);
    }

    match &sig.return_ty {
        Some(ty) => {
            visit_ty(&ty.node, records, variants);
        }
        None => {
            visit_ty(&mono::Type::unit(), records, variants);
        }
    }

    if let Some(ty) = &sig.exceptions {
        visit_ty(&ty.node, records, variants);
    }
}

fn visit_fields(
    fields: &mono::ConFields,
    records: &mut HashSet<RecordType>,
    variants: &mut HashSet<VariantType>,
) {
    match fields {
        mono::ConFields::Empty => {}

        mono::ConFields::Named(named_fields) => named_fields
            .iter()
            .for_each(|(_name, ty)| visit_ty(ty, records, variants)),

        mono::ConFields::Unnamed(fields) => {
            fields.iter().for_each(|ty| visit_ty(ty, records, variants))
        }
    }
}

fn visit_ty(
    ty: &mono::Type,
    records: &mut HashSet<RecordType>,
    variants: &mut HashSet<VariantType>,
) {
    match ty {
        mono::Type::Named(ty) => visit_named_ty(ty, records, variants),

        mono::Type::Record { fields } => {
            fields
                .values()
                .for_each(|field| visit_ty(field, records, variants));
            records.insert(RecordType {
                fields: fields.clone(),
            });
        }

        mono::Type::Variant { alts } => {
            alts.values()
                .for_each(|ty| visit_named_ty(ty, records, variants));
            variants.insert(VariantType { alts: alts.clone() });
        }

        mono::Type::Fn(mono::FnType { args, ret, exn }) => {
            match args {
                mono::FunArgs::Positional(args) => {
                    args.iter().for_each(|ty| visit_ty(ty, records, variants));
                }
                mono::FunArgs::Named(args) => {
                    args.values().for_each(|ty| visit_ty(ty, records, variants));
                }
            }
            visit_ty(ret, records, variants);
            visit_ty(exn, records, variants);
        }
    }
}

fn visit_named_ty(
    ty: &mono::NamedType,
    records: &mut HashSet<RecordType>,
    variants: &mut HashSet<VariantType>,
) {
    ty.args
        .iter()
        .for_each(|arg| visit_ty(arg, records, variants))
}

fn visit_stmt(
    stmt: &mono::Stmt,
    records: &mut HashSet<RecordType>,
    variants: &mut HashSet<VariantType>,
) {
    match stmt {
        mono::Stmt::Break { .. } | mono::Stmt::Continue { .. } => {}

        mono::Stmt::Let(mono::LetStmt { lhs, rhs }) => {
            visit_pat(&lhs.node, records, variants);
            visit_expr(&rhs.node, records, variants);
        }

        mono::Stmt::Assign(mono::AssignStmt { lhs, rhs }) => {
            visit_expr(&lhs.node, records, variants);
            visit_expr(&rhs.node, records, variants);
        }

        mono::Stmt::Expr(expr) => visit_expr(expr, records, variants),

        mono::Stmt::While(mono::WhileStmt {
            label: _,
            cond,
            body,
        }) => {
            visit_expr(&cond.node, records, variants);
            for stmt in body {
                visit_stmt(&stmt.node, records, variants);
            }
        }
    }
}

fn visit_pat(
    pat: &mono::Pat,
    records: &mut HashSet<RecordType>,
    variants: &mut HashSet<VariantType>,
) {
    match pat {
        mono::Pat::Var(_) | mono::Pat::Ignore | mono::Pat::Str(_) | mono::Pat::Char(_) => {}

        mono::Pat::Con(mono::ConPat { con: _, fields }) => {
            for field in fields {
                visit_pat(&field.node.node, records, variants);
            }
        }

        mono::Pat::Or(pat1, pat2) => {
            visit_pat(&pat1.node, records, variants);
            visit_pat(&pat2.node, records, variants);
        }

        mono::Pat::Record(mono::RecordPat { fields, ty }) => {
            ty.values().for_each(|ty| visit_ty(ty, records, variants));
            records.insert(RecordType { fields: ty.clone() });
            for field in fields {
                visit_pat(&field.node.node, records, variants);
            }
        }

        mono::Pat::Variant(mono::VariantPat { pat, ty }) => {
            ty.values()
                .for_each(|ty| visit_named_ty(ty, records, variants));
            variants.insert(VariantType { alts: ty.clone() });
            visit_pat(&pat.node, records, variants);
        }
    }
}

fn visit_expr(
    expr: &mono::Expr,
    records: &mut HashSet<RecordType>,
    variants: &mut HashSet<VariantType>,
) {
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
            visit_ty(ty, records, variants);
            visit_expr(&object.node, records, variants);
        }

        mono::Expr::Call(mono::CallExpr { fun, args, ty }) => {
            visit_ty(ty, records, variants);
            visit_expr(&fun.node, records, variants);
            for arg in args {
                visit_expr(&arg.expr.node, records, variants);
            }
        }

        mono::Expr::BoolOr(left, right) | mono::Expr::BoolAnd(left, right) => {
            visit_expr(&left.node, records, variants);
            visit_expr(&right.node, records, variants);
        }

        mono::Expr::Return(expr, ty) => {
            visit_ty(ty, records, variants);
            visit_expr(&expr.node, records, variants)
        }

        mono::Expr::Match(mono::MatchExpr {
            scrutinee,
            alts,
            ty,
        }) => {
            visit_ty(ty, records, variants);
            visit_expr(&scrutinee.node, records, variants);
            for alt in alts {
                visit_pat(&alt.pat.node, records, variants);
                if let Some(guard) = &alt.guard {
                    visit_expr(&guard.node, records, variants);
                }
                for stmt in &alt.rhs {
                    visit_stmt(&stmt.node, records, variants);
                }
            }
        }

        mono::Expr::If(mono::IfExpr {
            branches,
            else_branch,
            ty,
        }) => {
            visit_ty(ty, records, variants);
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

        mono::Expr::Fn(mono::FnExpr { sig, body }) => {
            visit_fun_sig(sig, records, variants);
            for stmt in body {
                visit_stmt(&stmt.node, records, variants);
            }
        }

        mono::Expr::Is(mono::IsExpr { expr, pat }) => {
            visit_expr(&expr.node, records, variants);
            visit_pat(&pat.node, records, variants);
        }

        mono::Expr::Do(stmts, ty) => {
            visit_ty(ty, records, variants);
            for stmt in stmts {
                visit_stmt(&stmt.node, records, variants);
            }
        }

        mono::Expr::Record(mono::RecordExpr { fields, ty }) => {
            ty.values().for_each(|ty| visit_ty(ty, records, variants));
            records.insert(RecordType { fields: ty.clone() });
            for (_field_name, field_expr) in fields {
                visit_expr(&field_expr.node, records, variants);
            }
        }

        mono::Expr::Variant(mono::VariantExpr { expr, ty }) => {
            ty.values()
                .for_each(|ty| visit_named_ty(ty, records, variants));
            variants.insert(VariantType { alts: ty.clone() });
            visit_expr(&expr.node, records, variants);
        }
    }
}
