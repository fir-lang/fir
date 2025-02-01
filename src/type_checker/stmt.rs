use crate::ast::{self, AssignOp, Id};
use crate::type_checker::convert::convert_ast_ty;
use crate::type_checker::expr::{check_expr, select_field};
use crate::type_checker::pat::check_pat;
use crate::type_checker::ty::*;
use crate::type_checker::unification::{unify, unify_expected_ty};
use crate::type_checker::{loc_display, TcFunState};

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

            unify_expected_ty(
                Ty::unit(),
                expected_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &stmt.loc,
            )
        }

        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => {
            let pat_expected_ty = ty
                .as_ref()
                .map(|ast_ty| convert_ast_ty(&tc_state.tys.tys, &ast_ty.node, &ast_ty.loc));

            tc_state.env.enter();
            let rhs_ty = check_expr(
                tc_state,
                rhs,
                pat_expected_ty.as_ref(),
                level + 1,
                loop_stack,
            );
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
                ast::Expr::Var(ast::VarExpr { id: var, ty_args }) => {
                    debug_assert!(ty_args.is_empty());
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
                    };

                    // `lhs.method(rhs)`
                    let desugared_rhs = ast::L {
                        loc: rhs.loc.clone(),
                        node: ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                loc: rhs.loc.clone(),
                                node: ast::Expr::FieldSelect(ast::FieldSelectExpr {
                                    object: Box::new(ast::L {
                                        loc: stmt.loc.clone(),
                                        node: ast::Expr::Var(ast::VarExpr {
                                            id: var.clone(),
                                            ty_args: vec![],
                                        }),
                                    }),
                                    field: SmolStr::new_static(method),
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

                ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
                    let object_ty = check_expr(tc_state, object, None, level, loop_stack);

                    let lhs_ty_normalized = object_ty.normalize(tc_state.tys.tys.cons());
                    let lhs_ty: Ty = match &lhs_ty_normalized {
                        Ty::Con(con) => select_field(tc_state, con, &[], field, &lhs.loc)
                            .unwrap_or_else(|| {
                                panic!(
                                    "{}: Type {} does not have field {}",
                                    loc_display(&lhs.loc),
                                    con,
                                    field
                                )
                            }),

                        Ty::App(con, args) => match args {
                            TyArgs::Positional(args) => select_field(
                                tc_state, con, args, field, &lhs.loc,
                            )
                            .unwrap_or_else(|| {
                                panic!(
                                    "{}: Type {} does not have field {}",
                                    loc_display(&lhs.loc),
                                    con,
                                    field
                                )
                            }),
                            TyArgs::Named(_) => panic!(),
                        },

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
                    };

                    // `lhs.method(rhs)`
                    let desugared_rhs = ast::L {
                        loc: rhs.loc.clone(),
                        node: ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                loc: rhs.loc.clone(),
                                node: ast::Expr::FieldSelect(ast::FieldSelectExpr {
                                    object: Box::new(lhs.clone()),
                                    field: SmolStr::new_static(method),
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

        ast::Stmt::Expr(expr) => check_expr(tc_state, expr, expected_ty, level, loop_stack),

        ast::Stmt::For(ast::ForStmt {
            label,
            pat,
            ty,
            expr,
            expr_ty,
            body,
        }) => {
            assert!(expr_ty.is_none());

            // Fresh `iter` for the predicate `Iterator[iter, item]`.
            let iterator_ty_var = tc_state
                .var_gen
                .new_var(level, Kind::Star, expr.loc.clone());

            // The type `item` for the predicate `Iterator[iter, item]`. This will the the pattern
            // type (when available) or a fresh type variable.
            let item_ty_var = ty
                .as_ref()
                .map(|ty| convert_ast_ty(&tc_state.tys.tys, ty, &stmt.loc))
                .unwrap_or_else(|| {
                    Ty::Var(
                        tc_state
                            .var_gen
                            .new_var(level, Kind::Star, expr.loc.clone()),
                    )
                });

            // Add predicate `Iterator[iter, item]`.
            tc_state.preds.insert(Pred {
                trait_: SmolStr::new_static("Iterator"),
                params: vec![Ty::Var(iterator_ty_var.clone()), item_ty_var.clone()],
                loc: stmt.loc.clone(),
            });

            *expr_ty = Some(check_expr(
                tc_state,
                expr,
                Some(&Ty::Var(iterator_ty_var.clone())),
                level,
                loop_stack,
            ));

            tc_state.env.enter();

            let pat_ty = check_pat(tc_state, pat, level);
            unify(
                &pat_ty,
                &item_ty_var,
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
            check_expr(tc_state, cond, Some(&Ty::bool()), level, loop_stack);
            loop_stack.push(label.clone());
            check_stmts(tc_state, body, None, level, loop_stack);
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

        ast::Stmt::WhileLet(ast::WhileLetStmt {
            label,
            pat,
            cond,
            body,
        }) => {
            tc_state.env.enter();
            let cond_ty = check_expr(tc_state, cond, None, level, loop_stack);
            tc_state.env.exit();

            let pat_ty = check_pat(tc_state, pat, level);

            unify(
                &pat_ty,
                &cond_ty,
                tc_state.tys.tys.cons(),
                tc_state.var_gen,
                level,
                &pat.loc,
            );

            tc_state.env.enter();
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
    }
}
