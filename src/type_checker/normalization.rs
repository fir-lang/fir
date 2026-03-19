use crate::ast::{self, Id};
use crate::collections::ScopeMap;
use crate::interpolation::StrPart;
use crate::type_checker::TyCon;
use crate::type_checker::traits::TraitEnv;
use crate::type_checker::ty::UVarGen;
use crate::utils::loc_display;

pub(super) fn normalize_stmt(
    stmt: &mut ast::Stmt,
    loc: &ast::Loc,
    cons: &ScopeMap<Id, TyCon>,
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
) {
    match stmt {
        ast::Stmt::Break { .. } | ast::Stmt::Continue { .. } => {}

        ast::Stmt::Let(ast::LetStmt { lhs, ty: _, rhs }) => {
            normalize_pat(&mut lhs.node, cons, trait_env, var_gen);
            normalize_expr(&mut rhs.node, &rhs.loc, cons, trait_env, var_gen);
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op: _ }) => {
            normalize_expr(&mut lhs.node, loc, cons, trait_env, var_gen);
            normalize_expr(&mut rhs.node, &rhs.loc, cons, trait_env, var_gen);
        }

        ast::Stmt::Expr(expr) => normalize_expr(expr, loc, cons, trait_env, var_gen),

        ast::Stmt::For(ast::ForStmt { .. }) => {
            panic!("{}: Non-desugared for statement", loc_display(loc));
        }

        ast::Stmt::While(ast::WhileStmt {
            label: _,
            cond,
            body,
        }) => {
            normalize_expr(&mut cond.node, &cond.loc, cons, trait_env, var_gen);
            for stmt in body {
                normalize_stmt(&mut stmt.node, &stmt.loc, cons, trait_env, var_gen);
            }
        }
    }
}

fn normalize_expr(
    expr: &mut ast::Expr,
    loc: &ast::Loc,
    cons: &ScopeMap<Id, TyCon>,
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
) {
    match expr {
        ast::Expr::Var(ast::VarExpr {
            ty_args,
            inferred_ty,
            ..
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap_or_else(|| panic!("{}", loc_display(loc)))
                    .deep_normalize(cons, trait_env, var_gen),
            );
            ty_args
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen))
        }

        ast::Expr::ConSel(ast::Con {
            ty_args,
            inferred_ty,
            ..
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap_or_else(|| panic!("{}", loc_display(loc)))
                    .deep_normalize(cons, trait_env, var_gen),
            );
            ty_args
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen));
        }

        ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
            ty_args,
            inferred_ty,
            ..
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            ty_args
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen))
        }

        ast::Expr::Int(_) | ast::Expr::Char(_) => {}

        ast::Expr::Str(parts) => parts.iter_mut().for_each(|part| match part {
            StrPart::Str(_) => {}
            StrPart::Expr(expr) => {
                normalize_expr(&mut expr.node, &expr.loc, cons, trait_env, var_gen)
            }
        }),

        ast::Expr::FieldSel(ast::FieldSelExpr {
            object,
            field: _,
            user_ty_args,
            inferred_ty,
        }) => {
            assert!(user_ty_args.is_empty());
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap_or_else(|| panic!("{}", loc_display(loc)))
                    .deep_normalize(cons, trait_env, var_gen),
            );
            normalize_expr(&mut object.node, &object.loc, cons, trait_env, var_gen)
        }

        ast::Expr::MethodSel(ast::MethodSelExpr {
            object,
            method_ty_id: _,
            method: _,
            ty_args,
            inferred_ty,
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            ty_args
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen));
            normalize_expr(&mut object.node, &object.loc, cons, trait_env, var_gen)
        }

        ast::Expr::Call(ast::CallExpr {
            fun,
            args,
            inferred_ty,
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            normalize_expr(&mut fun.node, &fun.loc, cons, trait_env, var_gen);
            for arg in args {
                normalize_expr(&mut arg.expr.node, &arg.expr.loc, cons, trait_env, var_gen);
            }
        }

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op: _ }) => {
            normalize_expr(&mut left.node, &left.loc, cons, trait_env, var_gen);
            normalize_expr(&mut right.node, &right.loc, cons, trait_env, var_gen);
        }

        ast::Expr::UnOp(ast::UnOpExpr { op: _, expr }) => {
            normalize_expr(&mut expr.node, &expr.loc, cons, trait_env, var_gen);
        }

        ast::Expr::Return(ast::ReturnExpr { expr, inferred_ty }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            normalize_expr(&mut expr.node, &expr.loc, cons, trait_env, var_gen);
        }

        ast::Expr::Match(ast::MatchExpr {
            scrutinee,
            alts,
            inferred_ty,
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            normalize_expr(
                &mut scrutinee.node,
                &scrutinee.loc,
                cons,
                trait_env,
                var_gen,
            );
            for ast::Alt { pat, guard, rhs } in alts {
                normalize_pat(&mut pat.node, cons, trait_env, var_gen);
                if let Some(expr) = guard {
                    normalize_expr(&mut expr.node, &expr.loc, cons, trait_env, var_gen);
                }
                for stmt in rhs {
                    normalize_stmt(&mut stmt.node, &stmt.loc, cons, trait_env, var_gen);
                }
            }
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
            inferred_ty,
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            for (cond, body) in branches {
                normalize_expr(&mut cond.node, &cond.loc, cons, trait_env, var_gen);
                for stmt in body {
                    normalize_stmt(&mut stmt.node, &stmt.loc, cons, trait_env, var_gen);
                }
            }
            if let Some(else_branch) = else_branch {
                for stmt in else_branch {
                    normalize_stmt(&mut stmt.node, &stmt.loc, cons, trait_env, var_gen);
                }
            }
        }

        ast::Expr::Fn(ast::FnExpr {
            sig: _,
            body,
            inferred_ty,
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            for stmt in body {
                normalize_stmt(&mut stmt.node, &stmt.loc, cons, trait_env, var_gen);
            }
        }

        ast::Expr::Is(ast::IsExpr { expr, pat }) => {
            normalize_expr(&mut expr.node, &expr.loc, cons, trait_env, var_gen);
            normalize_pat(&mut pat.node, cons, trait_env, var_gen);
        }

        ast::Expr::Do(ast::DoExpr { stmts, inferred_ty }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_ref()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            for stmt in stmts {
                normalize_stmt(&mut stmt.node, &stmt.loc, cons, trait_env, var_gen);
            }
        }

        ast::Expr::Seq { .. } => panic!("Seq expr should've been desugared"),

        ast::Expr::Record(ast::RecordExpr {
            fields,
            inferred_ty,
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_mut()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            for (_field_name, field_expr) in fields {
                normalize_expr(
                    &mut field_expr.node,
                    &field_expr.loc,
                    cons,
                    trait_env,
                    var_gen,
                );
            }
        }

        ast::Expr::Variant(ast::VariantExpr { expr, inferred_ty }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_mut()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            normalize_expr(&mut expr.node, &expr.loc, cons, trait_env, var_gen);
        }
    }
}

fn normalize_pat(
    pat: &mut ast::Pat,
    cons: &ScopeMap<Id, TyCon>,
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
) {
    match pat {
        ast::Pat::Var(ast::VarPat {
            var: _,
            ty,
            refined,
        }) => {
            *ty = Some(
                ty.as_ref()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            if let Some(ty) = refined {
                *ty = ty.deep_normalize(cons, trait_env, var_gen);
            }
        }

        ast::Pat::Ignore | ast::Pat::Str(_) | ast::Pat::Char(_) => {}

        ast::Pat::Con(ast::ConPat {
            con: ast::Con { ty_args, .. },
            fields,
            ignore_rest: _,
        }) => {
            for field in fields {
                normalize_pat(&mut field.node.node, cons, trait_env, var_gen);
            }
            for ty_arg in ty_args {
                *ty_arg = ty_arg.deep_normalize(cons, trait_env, var_gen);
            }
        }

        ast::Pat::Or(pat1, pat2) => {
            normalize_pat(&mut pat1.node, cons, trait_env, var_gen);
            normalize_pat(&mut pat2.node, cons, trait_env, var_gen);
        }

        ast::Pat::Record(ast::RecordPat {
            fields,
            ignore_rest: _,
            inferred_ty,
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_mut()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            fields.iter_mut().for_each(|ast::Named { name: _, node }| {
                normalize_pat(&mut node.node, cons, trait_env, var_gen)
            });
        }

        ast::Pat::Variant(ast::VariantPat {
            pat,
            inferred_ty,
            inferred_pat_ty,
        }) => {
            *inferred_ty = Some(
                inferred_ty
                    .as_mut()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            *inferred_pat_ty = Some(
                inferred_pat_ty
                    .as_mut()
                    .unwrap()
                    .deep_normalize(cons, trait_env, var_gen),
            );
            normalize_pat(&mut pat.node, cons, trait_env, var_gen);
        }
    }
}
