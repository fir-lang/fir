use crate::ast::{self, Id};
use crate::collections::ScopeMap;
use crate::interpolation::StringPart;
use crate::type_checker::TyCon;

pub(super) fn normalize_instantiation_types(stmt: &mut ast::Stmt, cons: &ScopeMap<Id, TyCon>) {
    match stmt {
        ast::Stmt::Break | ast::Stmt::Continue => {}

        ast::Stmt::Let(ast::LetStmt { lhs, ty: _, rhs }) => {
            normalize_pat(&mut lhs.node, cons);
            normalize_expr(&mut rhs.node, cons);
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op: _ }) => {
            normalize_expr(&mut lhs.node, cons);
            normalize_expr(&mut rhs.node, cons);
        }

        ast::Stmt::Expr(expr) => normalize_expr(&mut expr.node, cons),

        ast::Stmt::For(ast::ForStmt {
            var: _,
            ty: _,
            expr,
            expr_ty,
            body,
        }) => {
            normalize_expr(&mut expr.node, cons);
            for stmt in body {
                normalize_instantiation_types(&mut stmt.node, cons);
            }
            *expr_ty = Some(expr_ty.as_ref().unwrap().deep_normalize(cons));
        }

        ast::Stmt::While(ast::WhileStmt { cond, body }) => {
            normalize_expr(&mut cond.node, cons);
            for stmt in body {
                normalize_instantiation_types(&mut stmt.node, cons);
            }
        }
    }
}

fn normalize_expr(expr: &mut ast::Expr, cons: &ScopeMap<Id, TyCon>) {
    match expr {
        ast::Expr::Var(ast::VarExpr { ty_args, .. })
        | ast::Expr::Constr(ast::ConstrExpr { ty_args, .. })
        | ast::Expr::Variant(ast::ConstrExpr { ty_args, .. })
        | ast::Expr::ConstrSelect(ast::ConstrSelectExpr { ty_args, .. })
        | ast::Expr::AssocFnSelect(ast::AssocFnSelectExpr { ty_args, .. }) => ty_args
            .iter_mut()
            .for_each(|ty| *ty = ty.deep_normalize(cons)),

        ast::Expr::Int(_) | ast::Expr::Char(_) | ast::Expr::Self_ => {}

        ast::Expr::String(parts) => parts.iter_mut().for_each(|part| match part {
            StringPart::Str(_) => {}
            StringPart::Expr(expr) => normalize_expr(&mut expr.node, cons),
        }),

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field: _ }) => {
            normalize_expr(&mut object.node, cons)
        }

        ast::Expr::MethodSelect(ast::MethodSelectExpr {
            object,
            object_ty,
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

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            normalize_expr(&mut fun.node, cons);
            for arg in args {
                normalize_expr(&mut arg.expr.node, cons);
            }
        }

        ast::Expr::Range(ast::RangeExpr {
            from,
            to,
            inclusive: _,
        }) => {
            normalize_expr(&mut from.node, cons);
            normalize_expr(&mut to.node, cons);
        }

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op: _ }) => {
            normalize_expr(&mut left.node, cons);
            normalize_expr(&mut right.node, cons);
        }

        ast::Expr::UnOp(ast::UnOpExpr { op: _, expr }) => {
            normalize_expr(&mut expr.node, cons);
        }

        ast::Expr::Record(fields) => {
            for field in fields {
                normalize_expr(&mut field.node.node, cons);
            }
        }

        ast::Expr::Return(expr) => {
            normalize_expr(&mut expr.node, cons);
        }

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            normalize_expr(&mut scrutinee.node, cons);
            for ast::Alt {
                pattern,
                guard,
                rhs,
            } in alts
            {
                normalize_pat(&mut pattern.node, cons);
                if let Some(expr) = guard {
                    normalize_expr(&mut expr.node, cons);
                }
                for stmt in rhs {
                    normalize_instantiation_types(&mut stmt.node, cons);
                }
            }
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            for (cond, body) in branches {
                normalize_expr(&mut cond.node, cons);
                for stmt in body {
                    normalize_instantiation_types(&mut stmt.node, cons);
                }
            }
            if let Some(else_branch) = else_branch {
                for stmt in else_branch {
                    normalize_instantiation_types(&mut stmt.node, cons);
                }
            }
        }
    }
}

fn normalize_pat(pat: &mut ast::Pat, cons: &ScopeMap<Id, TyCon>) {
    match pat {
        ast::Pat::Var(_)
        | ast::Pat::Ignore
        | ast::Pat::Str(_)
        | ast::Pat::Char(_)
        | ast::Pat::StrPfx(_, _) => {}

        ast::Pat::Constr(ast::ConstrPattern {
            constr: _,
            fields,
            ty_args,
        }) => {
            for field in fields {
                normalize_pat(&mut field.node.node, cons);
            }
            for ty_arg in ty_args {
                *ty_arg = ty_arg.deep_normalize(cons);
            }
        }

        ast::Pat::Variant(_) => todo!(),

        ast::Pat::Record(fields) => fields
            .iter_mut()
            .for_each(|ast::Named { name: _, node }| normalize_pat(&mut node.node, cons)),

        ast::Pat::Or(pat1, pat2) => {
            normalize_pat(&mut pat1.node, cons);
            normalize_pat(&mut pat2.node, cons);
        }
    }
}
