use crate::ast::{self, AssignOp};
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
    loop_depth: u32,
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
            loop_depth,
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
    loop_depth: u32,
) -> Ty {
    match &mut stmt.node {
        ast::Stmt::Break | ast::Stmt::Continue => {
            if loop_depth == 0 {
                panic!(
                    "{}: `break` or `continue` statement not inside a loop",
                    loc_display(&stmt.loc)
                );
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
                loop_depth,
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
                            check_expr(tc_state, rhs, Some(&var_ty), level, loop_depth);
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

                    check_expr(tc_state, rhs, None, level, loop_depth);
                }

                ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
                    let object_ty = check_expr(tc_state, object, None, level, loop_depth);

                    let lhs_ty_normalized = object_ty.normalize(tc_state.tys.tys.cons());
                    let lhs_ty: Ty = match &lhs_ty_normalized {
                        Ty::Con(con) => select_field(con, &[], field, &lhs.loc, tc_state.tys)
                            .unwrap_or_else(|| {
                                panic!(
                                    "{}: Type {} does not have field {}",
                                    loc_display(&lhs.loc),
                                    con,
                                    field
                                )
                            }),

                        Ty::App(con, args) => match args {
                            TyArgs::Positional(args) => {
                                select_field(con, args, field, &lhs.loc, tc_state.tys)
                                    .unwrap_or_else(|| {
                                        panic!(
                                            "{}: Type {} does not have field {}",
                                            loc_display(&lhs.loc),
                                            con,
                                            field
                                        )
                                    })
                            }
                            TyArgs::Named(_) => panic!(),
                        },

                        Ty::Anonymous {
                            labels,
                            extension,
                            kind: RecordOrVariant::Record,
                            is_row,
                        } => {
                            assert_eq!(*is_row, false);
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
                            check_expr(tc_state, rhs, Some(&lhs_ty), level, loop_depth);
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

                    check_expr(tc_state, rhs, None, level, loop_depth);
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

        ast::Stmt::Expr(expr) => check_expr(tc_state, expr, expected_ty, level, loop_depth),

        ast::Stmt::For(ast::ForStmt {
            var,
            ty,
            expr,
            expr_ty,
            body,
        }) => {
            assert!(expr_ty.is_none());

            let ty = ty
                .as_ref()
                .map(|ty| convert_ast_ty(&tc_state.tys.tys, ty, &stmt.loc));

            // Expect the iterator to have fresh type `X` and add predicate `Iterator[X[Item = A]]`
            // with fresh type `A`.
            let iterator_ty = tc_state
                .var_gen
                .new_var(level, Kind::Star, expr.loc.clone());

            // TODO: loc should be the loc of `var`, which we don't have.
            let item_ty = ty.clone().unwrap_or_else(|| {
                Ty::Var(
                    tc_state
                        .var_gen
                        .new_var(level, Kind::Star, expr.loc.clone()),
                )
            });

            tc_state.preds.add(Pred {
                ty_var: iterator_ty.clone(),
                trait_: SmolStr::new_static("Iterator"),
                assoc_tys: [(SmolStr::new_static("Item"), item_ty.clone())]
                    .into_iter()
                    .collect(),
                loc: stmt.loc.clone(),
            });

            *expr_ty = Some(check_expr(
                tc_state,
                expr,
                Some(&Ty::Var(iterator_ty.clone())),
                level,
                loop_depth,
            ));

            tc_state.env.enter();
            tc_state.env.insert(var.clone(), item_ty);
            check_stmts(tc_state, body, None, level, loop_depth + 1);
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

        ast::Stmt::While(ast::WhileStmt { cond, body }) => {
            check_expr(tc_state, cond, Some(&Ty::bool()), level, loop_depth);
            check_stmts(tc_state, body, None, level, loop_depth + 1);
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
