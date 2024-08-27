use crate::ast;
use crate::scope_map::ScopeMap;
use crate::type_checker::convert::convert_ast_ty;
use crate::type_checker::expr::{check_expr, select_field};
use crate::type_checker::pat::check_pat;
use crate::type_checker::ty::*;
use crate::type_checker::unification::{unify, unify_expected_ty};
use crate::type_checker::{loc_string, PgmTypes};

use smol_str::SmolStr;

pub(super) fn check_stmts(
    stmts: &[ast::L<ast::Stmt>],
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
    preds: &mut PredSet,
) -> Ty {
    let num_stmts = stmts.len();
    assert!(num_stmts != 0);
    for (stmt_idx, stmt) in stmts.iter().enumerate() {
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
        );
        if last {
            return stmt_ty;
        }
    }
    panic!()
}

// TODO: Level is the same as the length of `env`, maybe remove the parameter?
fn check_stmt(
    stmt: &ast::L<ast::Stmt>,
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
    preds: &mut PredSet,
) -> Ty {
    match &stmt.node {
        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => {
            let pat_expected_ty = ty.as_ref().map(|ast_ty| {
                convert_ast_ty(&tys.cons, &Default::default(), &ast_ty.node, &ast_ty.loc)
            });

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
            );
            env.exit();

            let pat_ty = check_pat(lhs, level, env, var_gen, tys, preds);

            unify(&pat_ty, &rhs_ty, &tys.cons, &lhs.loc);

            unify_expected_ty(Ty::unit(), expected_ty, &tys.cons, &stmt.loc)
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op }) => {
            match &lhs.node {
                ast::Expr::Var(var) => {
                    let var_ty = env.get(var).cloned().unwrap_or_else(|| {
                        panic!("{}: Unbound variable {}", loc_string(&lhs.loc), var)
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
                            );
                            return Ty::unit();
                        }

                        ast::AssignOp::PlusEq => "__add",

                        ast::AssignOp::MinusEq => "__sub",
                    };

                    // `lhs.__add(rhs)` or `lhs.__sub(rhs)`
                    let desugared_rhs = ast::L {
                        loc: rhs.loc.clone(),
                        node: ast::Expr::Call(ast::CallExpr {
                            fun: Box::new(ast::L {
                                loc: rhs.loc.clone(),
                                node: ast::Expr::FieldSelect(ast::FieldSelectExpr {
                                    object: Box::new(ast::L {
                                        loc: stmt.loc.clone(),
                                        node: ast::Expr::Var(var.clone()),
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

                    check_expr(
                        &desugared_rhs,
                        None,
                        return_ty,
                        level,
                        env,
                        var_gen,
                        tys,
                        preds,
                    );
                }

                ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field }) => {
                    let object_ty =
                        check_expr(object, None, return_ty, level, env, var_gen, tys, preds);

                    let lhs_ty: Ty = match object_ty.normalize(&tys.cons) {
                        Ty::Con(con) => select_field(&con, &[], field, &lhs.loc, tys)
                            .unwrap_or_else(|| {
                                panic!(
                                    "{}: Type {} does not have field {}",
                                    loc_string(&lhs.loc),
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
                                    loc_string(&lhs.loc),
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
                                loc_string(&object.loc),
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
                            );
                            return Ty::unit();
                        }

                        ast::AssignOp::PlusEq => "__add",

                        ast::AssignOp::MinusEq => "__sub",
                    };

                    // `lhs.__add(rhs)` or `lhs.__sub(rhs)`
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

                    check_expr(
                        &desugared_rhs,
                        None,
                        return_ty,
                        level,
                        env,
                        var_gen,
                        tys,
                        preds,
                    );
                }

                _ => todo!("{}: Assignment with LHS: {:?}", loc_string(&lhs.loc), lhs),
            }

            unify_expected_ty(Ty::unit(), expected_ty, &tys.cons, &stmt.loc)
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
        ),

        ast::Stmt::For(_) => todo!(),

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
            );
            check_stmts(body, None, return_ty, level, env, var_gen, tys, preds);
            unify_expected_ty(Ty::unit(), expected_ty, &tys.cons, &stmt.loc)
        }
    }
}
