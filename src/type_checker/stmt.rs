use crate::ast;
use crate::collections::{Map, Set};
use crate::scope_map::ScopeMap;
use crate::type_checker::convert::convert_ast_ty;
use crate::type_checker::expr::check_expr;
use crate::type_checker::pat::check_pat;
use crate::type_checker::ty::*;
use crate::type_checker::unification::unify;
use crate::type_checker::PgmTypes;

pub(super) fn check_stmts(
    stmts: &[ast::L<ast::Stmt>],
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    quantified_vars: &Set<Id>,
    tys: &PgmTypes,
    preds: &mut Map<TyVarRef, Set<Id>>,
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
            quantified_vars,
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
    quantified_vars: &Set<Id>,
    tys: &PgmTypes,
    preds: &mut Map<TyVarRef, Set<Id>>,
) -> Ty {
    match &stmt.node {
        ast::Stmt::Let(ast::LetStmt { lhs, ty, rhs }) => {
            let pat_expected_ty = ty.as_ref().map(|ast_ty| {
                convert_ast_ty(&tys.cons, quantified_vars, &ast_ty.node, &ast_ty.loc)
            });

            env.enter();
            let rhs_ty = check_expr(
                rhs,
                pat_expected_ty.as_ref(),
                return_ty,
                level + 1,
                env,
                var_gen,
                quantified_vars,
                tys,
                preds,
            );
            env.exit();

            let pat_ty = check_pat(lhs, level, env, var_gen, tys);

            unify(&pat_ty, &rhs_ty, &lhs.loc);

            Ty::unit()
        }

        ast::Stmt::Assign(ast::AssignStmt {
            lhs: _,
            rhs: _,
            op: _,
        }) => todo!(),

        ast::Stmt::Expr(expr) => check_expr(
            expr,
            expected_ty,
            return_ty,
            level,
            env,
            var_gen,
            quantified_vars,
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
                quantified_vars,
                tys,
                preds,
            );
            check_stmts(
                body,
                None,
                return_ty,
                level,
                env,
                var_gen,
                quantified_vars,
                tys,
                preds,
            );
            Ty::unit()
        }
    }
}
