use crate::ast;
use crate::collections::ScopeMap;
use crate::type_checker::{Id, TyCon};

pub(super) fn normalize_instantiation_types(stmt: &mut ast::Stmt, cons: &ScopeMap<Id, TyCon>) {
    match stmt {
        ast::Stmt::Let(ast::LetStmt { lhs: _, ty: _, rhs }) => {
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
            body,
        }) => {
            normalize_expr(&mut expr.node, cons);
            for stmt in body {
                normalize_instantiation_types(&mut stmt.node, cons);
            }
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
        ast::Expr::Instantiation(_, tys) => tys.iter_mut().for_each(|ty| *ty = ty.normalize(cons)),

        ast::Expr::Var(_)
        | ast::Expr::UpperVar(_)
        | ast::Expr::ConstrSelect(_)
        | ast::Expr::Int(_)
        | ast::Expr::String(_)
        | ast::Expr::Char(_)
        | ast::Expr::Self_ => {}

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field: _ }) => {
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

        ast::Expr::ArrayIndex(ast::ArrayIndexExpr { array, index }) => {
            normalize_expr(&mut array.node, cons);
            normalize_expr(&mut index.node, cons);
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
            for alt in alts {
                for stmt in &mut alt.rhs {
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