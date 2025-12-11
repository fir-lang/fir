use crate::collections::Set;
use crate::mono_ast as mono;

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
    pub fn from_named_things<T>(things: &[mono::Named<T>]) -> RecordShape {
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

pub fn collect_records(pgm: &mono::MonoPgm) -> Set<RecordShape> {
    let mut records: Set<RecordShape> = Default::default();

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

fn visit_ty_decl(ty_decl: &mono::TypeDecl, records: &mut Set<RecordShape>) {
    match &ty_decl.rhs {
        None => {}

        Some(mono::TypeDeclRhs::Sum(constrs)) => {
            for constr in constrs {
                visit_fields(&constr.fields, records);
            }
        }

        Some(mono::TypeDeclRhs::Product(fields)) => {
            visit_fields(fields, records);
        }
    }
}

fn visit_fun_decl(fun_decl: &mono::FunDecl, records: &mut Set<RecordShape>) {
    visit_fun_sig(&fun_decl.sig, records);

    if let Some(body) = &fun_decl.body {
        for stmt in body {
            visit_stmt(&stmt.node, records);
        }
    }
}

fn visit_fun_sig(sig: &mono::FunSig, records: &mut Set<RecordShape>) {
    for (_param_name, param_ty) in &sig.params {
        visit_ty(&param_ty.node, records);
    }

    if let Some(return_ty) = &sig.return_ty {
        visit_ty(&return_ty.node, records);
    }
}

fn visit_fields(fields: &mono::ConstructorFields, records: &mut Set<RecordShape>) {
    match fields {
        mono::ConstructorFields::Empty => {}

        mono::ConstructorFields::Named(named_fields) => named_fields
            .iter()
            .for_each(|(_name, ty)| visit_ty(ty, records)),

        mono::ConstructorFields::Unnamed(fields) => {
            fields.iter().for_each(|ty| visit_ty(ty, records))
        }
    }
}

fn visit_ty(ty: &mono::Type, records: &mut Set<RecordShape>) {
    match ty {
        mono::Type::Named(mono::NamedType { name: _, args }) => {
            args.iter().for_each(|arg| visit_ty(arg, records))
        }

        mono::Type::Record { fields } => {
            records.insert(RecordShape::from_named_things(fields));
        }

        mono::Type::Variant { alts } => {
            for mono::NamedType { name: _, args } in alts {
                args.iter().for_each(|arg| visit_ty(arg, records))
            }
        }

        mono::Type::Fn(mono::FnType {
            args,
            ret,
            exceptions,
        }) => {
            match args {
                mono::FunArgs::Positional(args) => {
                    args.iter().for_each(|ty| visit_ty(ty, records));
                }
                mono::FunArgs::Named(args) => {
                    args.values().for_each(|ty| visit_ty(ty, records));
                }
            }
            if let Some(ret) = ret {
                visit_ty(&ret.node, records);
            }
            if let Some(exn) = exceptions {
                visit_ty(&exn.node, records);
            }
        }
    }
}

fn visit_stmt(stmt: &mono::Stmt, records: &mut Set<RecordShape>) {
    match stmt {
        mono::Stmt::Break { .. } | mono::Stmt::Continue { .. } => {}

        mono::Stmt::Let(mono::LetStmt { lhs, rhs }) => {
            visit_pat(&lhs.node, records);
            visit_expr(&rhs.node, records);
        }

        mono::Stmt::Assign(mono::AssignStmt { lhs, rhs, op: _ }) => {
            visit_expr(&lhs.node, records);
            visit_expr(&rhs.node, records);
        }

        mono::Stmt::Expr(expr) => visit_expr(&expr.node, records),

        mono::Stmt::For(mono::ForStmt {
            pat,
            expr,
            body,
            iter_ty,
            item_ty,
        }) => {
            visit_pat(&pat.node, records);
            visit_expr(&expr.node, records);
            for stmt in body {
                visit_stmt(&stmt.node, records);
            }
            visit_ty(iter_ty, records);
            visit_ty(item_ty, records);
        }

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

fn visit_pat(pat: &mono::Pat, records: &mut Set<RecordShape>) {
    match pat {
        mono::Pat::Var(_) | mono::Pat::Ignore | mono::Pat::Str(_) | mono::Pat::Char(_) => {}

        mono::Pat::Constr(mono::ConstrPattern { constr: _, fields }) => {
            for field in fields {
                visit_pat(&field.node.node, records);
            }
        }

        mono::Pat::Record(mono::RecordPattern { fields, ty }) => {
            for field in fields {
                visit_pat(&field.node.node, records);
            }
            visit_ty(ty, records);
        }

        mono::Pat::Or(pat1, pat2) => {
            visit_pat(&pat1.node, records);
            visit_pat(&pat2.node, records);
        }
    }
}

fn visit_expr(expr: &mono::Expr, records: &mut Set<RecordShape>) {
    match expr {
        mono::Expr::LocalVar(_)
        | mono::Expr::TopVar(_)
        | mono::Expr::ConstrSelect(_)
        | mono::Expr::AssocFnSelect(_)
        | mono::Expr::Int(_)
        | mono::Expr::Char(_) => {}

        mono::Expr::Str(parts) => {
            for part in parts {
                match part {
                    mono::StringPart::Str(_) => {}
                    mono::StringPart::Expr(expr) => visit_expr(&expr.node, records),
                }
            }
        }

        mono::Expr::FieldSelect(mono::FieldSelectExpr { object, field: _ }) => {
            visit_expr(&object.node, records);
        }

        mono::Expr::MethodSelect(mono::MethodSelectExpr {
            object,
            method_ty_id: _,
            method_id: _,
            ty_args: _,
        }) => {
            visit_expr(&object.node, records);
        }

        mono::Expr::Call(mono::CallExpr { fun, args }) => {
            visit_expr(&fun.node, records);
            for arg in args {
                visit_expr(&arg.expr.node, records);
            }
        }

        mono::Expr::BinOp(mono::BinOpExpr { left, right, op: _ }) => {
            visit_expr(&left.node, records);
            visit_expr(&right.node, records);
        }

        mono::Expr::Record(fields) => {
            for field in fields {
                visit_expr(&field.node.node, records);
            }
            records.insert(RecordShape::from_named_things(fields));
        }

        mono::Expr::Return(expr) => visit_expr(&expr.node, records),

        mono::Expr::Match(mono::MatchExpr { scrutinee, alts }) => {
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

        mono::Expr::Do(stmts) => {
            for stmt in stmts {
                visit_stmt(&stmt.node, records);
            }
        }
    }
}
