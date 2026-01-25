use crate::ast::{self, Id};
use crate::collections::ScopeMap;
use crate::interpolation::StrPart;
use crate::type_checker::TyCon;

pub(super) fn normalize_stmt(stmt: &mut ast::Stmt, cons: &ScopeMap<Id, TyCon>) {
    match stmt {
        ast::Stmt::Break { .. } | ast::Stmt::Continue { .. } => {}

        ast::Stmt::Let(ast::LetStmt { lhs, ty: _, rhs }) => {
            normalize_pat(&mut lhs.node, cons);
            normalize_expr(&mut rhs.node, cons);
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op: _ }) => {
            normalize_expr(&mut lhs.node, cons);
            normalize_expr(&mut rhs.node, cons);
        }

        ast::Stmt::Expr(expr) => normalize_expr(expr, cons),

        ast::Stmt::For(ast::ForStmt {
            label: _,
            pat,
            item_ast_ty: _,
            item_tc_ty,
            expr,
            expr_ty,
            body,
        }) => {
            if let Some(tc_ty) = item_tc_ty {
                *tc_ty = tc_ty.deep_normalize(cons);
            }
            normalize_pat(&mut pat.node, cons);
            normalize_expr(&mut expr.node, cons);
            for stmt in body {
                normalize_stmt(&mut stmt.node, cons);
            }
            *expr_ty = Some(expr_ty.as_ref().unwrap().deep_normalize(cons));
        }

        ast::Stmt::While(ast::WhileStmt {
            label: _,
            cond,
            body,
        }) => {
            normalize_expr(&mut cond.node, cons);
            for stmt in body {
                normalize_stmt(&mut stmt.node, cons);
            }
        }
    }
}

fn normalize_expr(expr: &mut ast::Expr, cons: &ScopeMap<Id, TyCon>) {
    match expr {
        ast::Expr::Var(ast::VarExpr { ty_args, .. })
        | ast::Expr::ConSel(ast::Con { ty_args, .. })
        | ast::Expr::AssocFnSel(ast::AssocFnSelExpr { ty_args, .. }) => ty_args
            .iter_mut()
            .for_each(|ty| *ty = ty.deep_normalize(cons)),

        ast::Expr::Int(_) | ast::Expr::Char(_) => {}

        ast::Expr::Str(parts) => parts.iter_mut().for_each(|part| match part {
            StrPart::Str(_) => {}
            StrPart::Expr(expr) => normalize_expr(&mut expr.node, cons),
        }),

        ast::Expr::FieldSel(ast::FieldSelExpr {
            object,
            field: _,
            user_ty_args,
        }) => {
            assert!(user_ty_args.is_empty());
            normalize_expr(&mut object.node, cons)
        }

        ast::Expr::MethodSel(ast::MethodSelExpr {
            object,
            object_ty,
            method_ty_id: _,
            method: _,
            ty_args,
        }) => {
            if let Some(object_ty) = object_ty {
                *object_ty = object_ty.deep_normalize(cons);
            }
            ty_args
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons));
            normalize_expr(&mut object.node, cons)
        }

        ast::Expr::Call(ast::CallExpr {
            fun,
            args,
            inferred_ty: _,
        }) => {
            normalize_expr(&mut fun.node, cons);
            for arg in args {
                normalize_expr(&mut arg.expr.node, cons);
            }
        }

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op: _ }) => {
            normalize_expr(&mut left.node, cons);
            normalize_expr(&mut right.node, cons);
        }

        ast::Expr::UnOp(ast::UnOpExpr { op: _, expr }) => {
            normalize_expr(&mut expr.node, cons);
        }

        ast::Expr::Return(ast::ReturnExpr { expr, inferred_ty }) => {
            normalize_expr(&mut expr.node, cons);
            if let Some(inferred_ty) = inferred_ty.as_mut() {
                *inferred_ty = inferred_ty.deep_normalize(cons);
            }
        }

        ast::Expr::Match(ast::MatchExpr {
            scrutinee,
            alts,
            inferred_ty,
        }) => {
            normalize_expr(&mut scrutinee.node, cons);
            for ast::Alt { pat, guard, rhs } in alts {
                normalize_pat(&mut pat.node, cons);
                if let Some(expr) = guard {
                    normalize_expr(&mut expr.node, cons);
                }
                for stmt in rhs {
                    normalize_stmt(&mut stmt.node, cons);
                }
            }
            if let Some(inferred_ty) = inferred_ty.as_mut() {
                *inferred_ty = inferred_ty.deep_normalize(cons);
            }
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
            inferred_ty,
        }) => {
            for (cond, body) in branches {
                normalize_expr(&mut cond.node, cons);
                for stmt in body {
                    normalize_stmt(&mut stmt.node, cons);
                }
            }
            if let Some(else_branch) = else_branch {
                for stmt in else_branch {
                    normalize_stmt(&mut stmt.node, cons);
                }
            }
            if let Some(inferred_ty) = inferred_ty.as_mut() {
                *inferred_ty = inferred_ty.deep_normalize(cons);
            }
        }

        ast::Expr::Fn(ast::FnExpr {
            sig: _,
            body,
            inferred_ty,
        }) => {
            for stmt in body {
                normalize_stmt(&mut stmt.node, cons);
            }
            if let Some(inferred_ty) = inferred_ty.as_mut() {
                *inferred_ty = inferred_ty.deep_normalize(cons);
            }
        }

        ast::Expr::Is(ast::IsExpr { expr, pat }) => {
            normalize_expr(&mut expr.node, cons);
            normalize_pat(&mut pat.node, cons);
        }

        ast::Expr::Do(ast::DoExpr { stmts, inferred_ty }) => {
            for stmt in stmts {
                normalize_stmt(&mut stmt.node, cons);
            }
            if let Some(inferred_ty) = inferred_ty.as_mut() {
                *inferred_ty = inferred_ty.deep_normalize(cons);
            }
        }

        ast::Expr::Seq { .. } => panic!("Seq expr should've been desugared"),

        ast::Expr::Record(ast::RecordExpr {
            fields,
            inferred_ty,
        }) => {
            for (_field_name, field_expr) in fields {
                normalize_expr(&mut field_expr.node, cons);
            }
            *inferred_ty = Some(inferred_ty.as_mut().unwrap().deep_normalize(cons));
        }

        ast::Expr::Variant(ast::VariantExpr { expr, inferred_ty }) => {
            normalize_expr(&mut expr.node, cons);
            *inferred_ty = Some(inferred_ty.as_mut().unwrap().deep_normalize(cons));
        }
    }
}

fn normalize_pat(pat: &mut ast::Pat, cons: &ScopeMap<Id, TyCon>) {
    match pat {
        ast::Pat::Var(ast::VarPat { var: _, ty }) => {
            *ty = Some(ty.as_ref().unwrap().deep_normalize(cons));
        }

        ast::Pat::Ignore | ast::Pat::Str(_) | ast::Pat::Char(_) => {}

        ast::Pat::Con(ast::ConPat {
            con: ast::Con { ty_args, .. },
            fields,
            ignore_rest: _,
        }) => {
            for field in fields {
                normalize_pat(&mut field.node.node, cons);
            }
            for ty_arg in ty_args {
                *ty_arg = ty_arg.deep_normalize(cons);
            }
        }

        ast::Pat::Or(pat1, pat2) => {
            normalize_pat(&mut pat1.node, cons);
            normalize_pat(&mut pat2.node, cons);
        }

        ast::Pat::Record(ast::RecordPat {
            fields,
            ignore_rest: _,
            inferred_ty,
        }) => {
            fields
                .iter_mut()
                .for_each(|ast::Named { name: _, node }| normalize_pat(&mut node.node, cons));
            *inferred_ty = Some(inferred_ty.as_mut().unwrap().deep_normalize(cons));
        }

        ast::Pat::Variant(ast::VariantPat { pat, inferred_ty }) => {
            normalize_pat(&mut pat.node, cons);
            *inferred_ty = Some(inferred_ty.as_mut().unwrap().deep_normalize(cons));
        }
    }
}
