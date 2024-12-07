use crate::ast::{self, AssignOp, Id};
use crate::scope_map::ScopeMap;
use crate::type_checker::convert::convert_ast_ty;
use crate::type_checker::expr::{check_expr, select_field};
use crate::type_checker::pat::check_pat;
use crate::type_checker::ty::*;
use crate::type_checker::unification::{unify, unify_expected_ty};
use crate::type_checker::{loc_display, PgmTypes};

use smol_str::SmolStr;

pub(super) fn check_stmts(
    stmts: &mut [ast::L<ast::Stmt>],
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
    preds: &mut PredSet,
    loop_depth: u32,
) -> Ty {
    let num_stmts = stmts.len();
    assert!(num_stmts != 0);
    for (stmt_idx, stmt) in stmts.iter_mut().enumerate() {
        let last = stmt_idx == num_stmts - 1;
        let stmt_ty = check_stmt(
            stmt,
            if last { expected_ty } else { None },
            return_ty,
            level,
            env,
            var_gen,
            tys,
            preds,
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
    stmt: &mut ast::L<ast::Stmt>,
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
    preds: &mut PredSet,
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
            unify_expected_ty(Ty::unit(), expected_ty, tys.tys.cons(), &stmt.loc)
        }

        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => {
            let pat_expected_ty = ty
                .as_ref()
                .map(|ast_ty| convert_ast_ty(&tys.tys, &ast_ty.node, &ast_ty.loc));

            env.enter();
            let rhs_ty = check_expr(
                rhs,
                pat_expected_ty.as_ref(),
                return_ty,
                level + 1,
                env,
                var_gen,
                tys,
                preds,
                loop_depth,
            );
            env.exit();

            let pat_ty = check_pat(lhs, level, env, var_gen, tys, preds);

            unify(&pat_ty, &rhs_ty, tys.tys.cons(), &lhs.loc);

            unify_expected_ty(Ty::unit(), expected_ty, tys.tys.cons(), &stmt.loc)
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op }) => {
            match &mut lhs.node {
                ast::Expr::Var(ast::VarExpr { id: var, ty_args }) => {
                    debug_assert!(ty_args.is_empty());
                    let var_ty = env.get(var).cloned().unwrap_or_else(|| {
                        panic!("{}: Unbound variable {}", loc_display(&lhs.loc), var)
                    });

                    let method = match op {
                        ast::AssignOp::Eq => {
                            check_expr(
                                rhs,
                                Some(&var_ty),
                                return_ty,
                                level,
                                env,
                                var_gen,
                                tys,
                                preds,
                                loop_depth,
                            );
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

                    check_expr(
                        rhs, None, return_ty, level, env, var_gen, tys, preds, loop_depth,
                    );
                }

                ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
                    let object_ty = check_expr(
                        object, None, return_ty, level, env, var_gen, tys, preds, loop_depth,
                    );

                    let lhs_ty: Ty = match object_ty.normalize(tys.tys.cons()) {
                        Ty::Con(con) => select_field(&con, &[], field, &lhs.loc, tys)
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
                                &con, &args, field, &lhs.loc, tys,
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

                        Ty::Record(fields) => match fields.get(field) {
                            Some(field_ty) => field_ty.clone(),
                            None => panic!(
                                "{}: Record with fields {:?} does not have field {}",
                                loc_display(&object.loc),
                                fields.keys().collect::<Vec<_>>(),
                                field
                            ),
                        },

                        _ => panic!(),
                    };

                    let method = match op {
                        ast::AssignOp::Eq => {
                            check_expr(
                                rhs,
                                Some(&lhs_ty),
                                return_ty,
                                level,
                                env,
                                var_gen,
                                tys,
                                preds,
                                loop_depth,
                            );
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

                    check_expr(
                        rhs, None, return_ty, level, env, var_gen, tys, preds, loop_depth,
                    );
                }

                _ => todo!("{}: Assignment with LHS: {:?}", loc_display(&lhs.loc), lhs),
            }

            unify_expected_ty(Ty::unit(), expected_ty, tys.tys.cons(), &stmt.loc)
        }

        ast::Stmt::Expr(expr) => check_expr(
            expr,
            expected_ty,
            return_ty,
            level,
            env,
            var_gen,
            tys,
            preds,
            loop_depth,
        ),

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
                .map(|ty| convert_ast_ty(&tys.tys, ty, &stmt.loc));

            // Expect the iterator to have fresh type `X` and add predicate `Iterator[X[Item = A]]`
            // with fresh type `A`.
            let iterator_ty = var_gen.new_var(level, expr.loc.clone());

            // TODO: loc should be the loc of `var`, which we don't have.
            let item_ty = ty
                .clone()
                .unwrap_or_else(|| Ty::Var(var_gen.new_var(level, expr.loc.clone())));

            preds.add(Pred {
                ty_var: iterator_ty.clone(),
                trait_: SmolStr::new_static("Iterator"),
                assoc_tys: [(SmolStr::new_static("Item"), item_ty.clone())]
                    .into_iter()
                    .collect(),
                loc: stmt.loc.clone(),
            });

            *expr_ty = Some(check_expr(
                expr,
                Some(&Ty::Var(iterator_ty.clone())),
                return_ty,
                level,
                env,
                var_gen,
                tys,
                preds,
                loop_depth,
            ));

            env.enter();
            env.insert(var.clone(), item_ty);
            check_stmts(
                body,
                None,
                return_ty,
                level,
                env,
                var_gen,
                tys,
                preds,
                loop_depth + 1,
            );
            env.exit();
            unify_expected_ty(Ty::unit(), expected_ty, tys.tys.cons(), &stmt.loc)
        }

        ast::Stmt::While(ast::WhileStmt { cond, body }) => {
            check_expr(
                cond,
                Some(&Ty::bool()),
                return_ty,
                level,
                env,
                var_gen,
                tys,
                preds,
                loop_depth,
            );
            check_stmts(
                body,
                None,
                return_ty,
                level,
                env,
                var_gen,
                tys,
                preds,
                loop_depth + 1,
            );
            unify_expected_ty(Ty::unit(), expected_ty, tys.tys.cons(), &stmt.loc)
        }
    }
}
