use crate::ast::{self, AssignOp, Id};
use crate::type_checker::convert::convert_ast_ty;
use crate::type_checker::expr::{check_expr, select_field};
use crate::type_checker::pat::check_pat;
use crate::type_checker::ty::*;
use crate::type_checker::unification::{unify, unify_expected_ty};
use crate::type_checker::{TcFunState, loc_display};

use smol_str::SmolStr;

pub(super) fn check_stmts(
    tc_state: &mut TcFunState,
    stmts: &mut [ast::L<ast::Stmt>],
    expected_ty: Option<&Ty>,
    level: u32,
    loop_stack: &mut Vec<Option<Id>>,
) -> Ty {
    let num_stmts = stmts.len();
    assert!(num_stmts != 0);
    for (stmt_idx, stmt) in stmts.iter_mut().enumerate() {
        let last = stmt_idx == num_stmts - 1;
        let stmt_ty = check_stmt(
            tc_state,
            stmt,
            if last { expected_ty } else { None },
            level,
            loop_stack,
        );
        if last {
            return stmt_ty;
        }
    }
    panic!()
}

// TODO: Level is the same as the length of `env`, maybe remove the parameter?
fn check_stmt(
    tc_state: &mut TcFunState,
    stmt: &mut ast::L<ast::Stmt>,
    expected_ty: Option<&Ty>,
    level: u32,
    loop_stack: &mut Vec<Option<Id>>,
) -> Ty {
    match &mut stmt.node {
        ast::Stmt::Break {
            label,
            level: loop_level,
        }
        | ast::Stmt::Continue {
            label,
            level: loop_level,
        } => {
            assert_eq!(*loop_level, 0);

            if loop_stack.is_empty() {
                panic!(
                    "{}: `break` or `continue` statement not inside a loop",
                    loc_display(&stmt.loc)
                );
            }

            if let Some(label) = label {
                match loop_stack
                    .iter()
                    .rev()
                    .enumerate()
                    .find(|id| id.1.as_ref() == Some(label))
                {
                    Some((depth, _)) => {
                        *loop_level = depth as u32;
                    }
                    None => {
                        panic!("{}: no loop with label {}", loc_display(&stmt.loc), label);
                    }
                }
            }

            expected_ty.cloned().unwrap_or_else(|| {
                Ty::UVar(
                    tc_state
                        .var_gen
                        .new_var(level, Kind::Star, stmt.loc.clone()),
                )
            })
        }

        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => {
            let pat_expected_ty = ty
                .as_ref()
                .map(|ast_ty| convert_ast_ty(&tc_state.tys.tys, &ast_ty.node, &ast_ty.loc))
                .unwrap_or_else(|| {
                    Ty::UVar(tc_state.var_gen.new_var(level, Kind::Star, lhs.loc.clone()))
                });

            tc_state.env.enter();
            let (rhs_ty, _) =
                check_expr(tc_state, rhs, Some(&pat_expected_ty), level + 1, loop_stack);
            tc_state.env.exit();

            let pat_ty = check_pat(tc_state, lhs, level);

            unify(
                &pat_ty,
                &rhs_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &lhs.loc,
            );

            unify_expected_ty(
                Ty::unit(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &stmt.loc,
            )
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op }) => {
            match &mut lhs.node {
                ast::Expr::Var(ast::VarExpr {
                    id: var,
                    user_ty_args,
                    ty_args,
                }) => {
                    assert!(ty_args.is_empty());
                    assert!(user_ty_args.is_empty());
                    let var_ty = tc_state.env.get(var).cloned().unwrap_or_else(|| {
                        panic!("{}: Unbound variable {}", loc_display(&lhs.loc), var)
                    });

                    let method = match op {
                        ast::AssignOp::Eq => {
                            check_expr(tc_state, rhs, Some(&var_ty), level, loop_stack);
                            return Ty::unit();
                        }

                        ast::AssignOp::PlusEq => "__add",

                        ast::AssignOp::MinusEq => "__sub",

                        ast::AssignOp::StarEq => "__mul",

                        ast::AssignOp::CaretEq => "__bitxor",
                    };

                    // `lhs.method(rhs)`
                    let desugared_rhs = ast::L {
                        loc: rhs.loc.clone(),
                        node: ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                loc: rhs.loc.clone(),
                                node: ast::Expr::FieldSel(ast::FieldSelExpr {
                                    object: Box::new(ast::L {
                                        loc: stmt.loc.clone(),
                                        node: ast::Expr::Var(ast::VarExpr {
                                            id: var.clone(),
                                            user_ty_args: vec![],
                                            ty_args: vec![],
                                        }),
                                    }),
                                    field: SmolStr::new_static(method),
                                    user_ty_args: vec![],
                                }),
                            }),
                            args: vec![ast::CallArg {
                                name: None,
                                expr: (*rhs).clone(),
                            }],
                        }),
                    };

                    *rhs = desugared_rhs;
                    *op = AssignOp::Eq;

                    check_expr(tc_state, rhs, None, level, loop_stack);
                }

                ast::Expr::FieldSel(ast::FieldSelExpr {
                    object,
                    field,
                    user_ty_args,
                }) => {
                    assert!(user_ty_args.is_empty());

                    let (object_ty, _) = check_expr(tc_state, object, None, level, loop_stack);

                    let lhs_ty_normalized = object_ty.normalize(tc_state.tys.tys.cons());
                    let lhs_ty: Ty = match &lhs_ty_normalized {
                        Ty::Con(con, _) => select_field(tc_state, con, &[], field, &lhs.loc)
                            .unwrap_or_else(|| {
                                panic!(
                                    "{}: Type {} does not have field {}",
                                    loc_display(&lhs.loc),
                                    con,
                                    field
                                )
                            }),

                        Ty::App(con, args, _) => select_field(tc_state, con, args, field, &lhs.loc)
                            .unwrap_or_else(|| {
                                panic!(
                                    "{}: Type {} does not have field {}",
                                    loc_display(&lhs.loc),
                                    con,
                                    field
                                )
                            }),

                        Ty::Anonymous {
                            labels,
                            extension,
                            kind: RecordOrVariant::Record,
                            is_row,
                        } => {
                            assert!(!(*is_row));
                            let (fields, _) = crate::type_checker::row_utils::collect_rows(
                                tc_state.tys.tys.cons(),
                                &lhs_ty_normalized,
                                RecordOrVariant::Record,
                                labels,
                                extension.clone(),
                            );
                            match fields.get(field) {
                                Some(field_ty) => field_ty.clone(),
                                None => panic!(
                                    "{}: Record with fields {:?} does not have field {}",
                                    loc_display(&object.loc),
                                    fields.keys().collect::<Vec<_>>(),
                                    field
                                ),
                            }
                        }

                        _ => panic!(),
                    };

                    let method = match op {
                        ast::AssignOp::Eq => {
                            check_expr(tc_state, rhs, Some(&lhs_ty), level, loop_stack);
                            return Ty::unit();
                        }

                        ast::AssignOp::PlusEq => "__add",

                        ast::AssignOp::MinusEq => "__sub",

                        ast::AssignOp::StarEq => "__mul",

                        ast::AssignOp::CaretEq => "__bitxor",
                    };

                    // `lhs.method(rhs)`
                    let desugared_rhs = ast::L {
                        loc: rhs.loc.clone(),
                        node: ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                loc: rhs.loc.clone(),
                                node: ast::Expr::FieldSel(ast::FieldSelExpr {
                                    object: Box::new(lhs.clone()),
                                    field: SmolStr::new_static(method),
                                    user_ty_args: vec![],
                                }),
                            }),
                            args: vec![ast::CallArg {
                                name: None,
                                expr: (*rhs).clone(),
                            }],
                        }),
                    };

                    *rhs = desugared_rhs;
                    *op = AssignOp::Eq;

                    check_expr(tc_state, rhs, None, level, loop_stack);
                }

                _ => todo!("{}: Assignment with LHS: {:?}", loc_display(&lhs.loc), lhs),
            }

            unify_expected_ty(
                Ty::unit(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &stmt.loc,
            )
        }

        ast::Stmt::Expr(ast::L {
            node: ast::Expr::Match(match_expr),
            loc,
        }) if expected_ty.is_none() => {
            crate::type_checker::expr::check_match_expr(
                tc_state, match_expr, loc, None, level, loop_stack,
            );
            Ty::unit()
        }

        ast::Stmt::Expr(ast::L {
            node: ast::Expr::If(if_expr),
            loc: _,
        }) if expected_ty.is_none() => {
            crate::type_checker::expr::check_if_expr(tc_state, if_expr, None, level, loop_stack);
            Ty::unit()
        }

        ast::Stmt::Expr(expr) => check_expr(tc_state, expr, expected_ty, level, loop_stack).0,

        ast::Stmt::For(ast::ForStmt {
            label,
            pat,
            item_ast_ty,
            item_tc_ty,
            expr,
            expr_ty,
            body,
        }) => {
            assert!(expr_ty.is_none());

            let iter_ty = check_expr(tc_state, expr, None, level, loop_stack).0;
            *expr_ty = Some(iter_ty.clone());

            // The type `item` for the predicate `Iterator[iter, item, exn]`. This will the the
            // pattern type (when available) or a fresh type variable.
            let item_ty = item_ast_ty
                .as_ref()
                .map(|ty| convert_ast_ty(&tc_state.tys.tys, &ty.node, &ty.loc))
                .unwrap_or_else(|| {
                    Ty::UVar(
                        tc_state
                            .var_gen
                            .new_var(level, Kind::Star, expr.loc.clone()),
                    )
                });

            *item_tc_ty = Some(item_ty.clone());

            // Add predicate `Iterator[iter, item, exn]`.
            tc_state.preds.push(Pred {
                trait_: SmolStr::new_static("Iterator"),
                params: vec![
                    iter_ty.clone(),
                    item_ty.clone(),
                    tc_state.exceptions.clone(),
                ],
                loc: stmt.loc.clone(),
            });

            tc_state.env.enter();

            let pat_ty = check_pat(tc_state, pat, level);
            unify(
                &pat_ty,
                &item_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &pat.loc,
            );

            loop_stack.push(label.clone());
            check_stmts(tc_state, body, None, level, loop_stack);
            loop_stack.pop();

            tc_state.env.exit();
            unify_expected_ty(
                Ty::unit(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &stmt.loc,
            )
        }

        ast::Stmt::While(ast::WhileStmt { label, cond, body }) => {
            let (_cond_ty, cond_binders) =
                check_expr(tc_state, cond, Some(&Ty::bool()), level, loop_stack);
            loop_stack.push(label.clone());
            tc_state.env.enter();
            cond_binders.into_iter().for_each(|(k, v)| {
                tc_state.env.insert(k, v);
            });
            check_stmts(tc_state, body, None, level, loop_stack);
            tc_state.env.exit();
            loop_stack.pop();
            unify_expected_ty(
                Ty::unit(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &stmt.loc,
            )
        }
    }
}
