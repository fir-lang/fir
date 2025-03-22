use crate::collections::{Map, ScopeSet};
use crate::mono_ast as mono;
use crate::mono_ast::Id;

#[derive(Debug)]
pub struct Closure {
    pub mono: mono::FnExpr,

    /// Maps free variables to their index in the closure's payload.
    pub fvs: Map<Id, u32>,
}

pub fn collect_closures(pgm: &mut mono::MonoPgm) -> Vec<Closure> {
    let mut closures: Vec<Closure> = vec![];

    for ty_map in pgm.funs.values_mut() {
        for fun in ty_map.values_mut() {
            visit_fun_decl(fun, &mut closures);
        }
    }

    for method_map in pgm.associated.values_mut() {
        for ty_map in method_map.values_mut() {
            for fun in ty_map.values_mut() {
                visit_fun_decl(fun, &mut closures);
            }
        }
    }

    closures
}

fn visit_fun_decl(decl: &mut mono::FunDecl, closures: &mut Vec<Closure>) {
    let mut local_vars: ScopeSet<Id> = Default::default();

    for (param, _) in &decl.sig.params {
        local_vars.insert(param.clone());
    }

    if let Some(body) = &mut decl.body {
        for stmt in body.iter_mut() {
            visit_stmt(
                &mut stmt.node,
                closures,
                &mut local_vars,
                &mut Default::default(),
            );
        }
    }
}

fn visit_stmt(
    decl: &mut mono::Stmt,
    closures: &mut Vec<Closure>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, u32>,
) {
    match decl {
        mono::Stmt::Let(mono::LetStmt { lhs, rhs }) => {
            bind_pat_binders(&lhs.node, local_vars);
            visit_expr(&mut rhs.node, closures, local_vars, free_vars);
        }

        mono::Stmt::Assign(mono::AssignStmt { lhs, rhs, op: _ }) => {
            visit_expr(&mut lhs.node, closures, local_vars, free_vars);
            visit_expr(&mut rhs.node, closures, local_vars, free_vars);
        }

        mono::Stmt::Expr(expr) => {
            visit_expr(&mut expr.node, closures, local_vars, free_vars);
        }

        mono::Stmt::For(mono::ForStmt {
            label: _,
            pat,
            expr,
            body,
        }) => {
            visit_expr(&mut expr.node, closures, local_vars, free_vars);
            local_vars.enter();
            bind_pat_binders(&pat.node, local_vars);
            for stmt in body {
                visit_stmt(&mut stmt.node, closures, local_vars, free_vars);
            }
            local_vars.exit();
        }

        mono::Stmt::While(mono::WhileStmt {
            label: _,
            cond,
            body,
        }) => {
            visit_expr(&mut cond.node, closures, local_vars, free_vars);
            local_vars.enter();
            for stmt in body.iter_mut() {
                visit_stmt(&mut stmt.node, closures, local_vars, free_vars);
            }
            local_vars.exit();
        }

        mono::Stmt::WhileLet(mono::WhileLetStmt {
            label: _,
            pat: _,
            cond,
            body,
        }) => {
            local_vars.enter();
            visit_expr(&mut cond.node, closures, local_vars, free_vars);
            local_vars.exit();

            local_vars.enter();
            for stmt in body.iter_mut() {
                visit_stmt(&mut stmt.node, closures, local_vars, free_vars);
            }
            local_vars.exit();
        }

        mono::Stmt::Break { .. } | mono::Stmt::Continue { .. } => {}
    }
}

fn visit_expr(
    expr: &mut mono::Expr,
    closures: &mut Vec<Closure>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, u32>,
) {
    match expr {
        //------------------------------------------------------------------------------------------
        mono::Expr::Fn(mono::FnExpr { sig, body, idx }) => {
            assert_eq!(*idx, 0);

            let mut fn_local_vars: ScopeSet<Id> = Default::default();
            for (param, _) in &sig.params {
                fn_local_vars.insert(param.clone());
            }

            let mut fn_free_vars: Map<Id, u32> = Default::default();

            for stmt in body.iter_mut() {
                visit_stmt(
                    &mut stmt.node,
                    closures,
                    &mut fn_local_vars,
                    &mut fn_free_vars,
                );
            }

            let closure_idx = closures.len() as u32;
            *idx = closure_idx;
            closures.push(Closure {
                mono: mono::FnExpr {
                    sig: sig.clone(),
                    body: body.clone(),
                    idx: closure_idx,
                },
                fvs: fn_free_vars.clone(),
            });

            // Add free vars of the nested closure that are not defined in the enclosing function as
            // free in the enclosing closure.
            for (fv, _) in fn_free_vars {
                if !local_vars.is_bound(&fv) {
                    let idx = free_vars.len() as u32;
                    free_vars.insert(fv, idx);
                }
            }
        }

        mono::Expr::LocalVar(id) => {
            if !local_vars.is_bound(id) {
                let idx = free_vars.len() as u32;
                free_vars.insert(id.clone(), idx);
            }
        }

        //------------------------------------------------------------------------------------------
        mono::Expr::TopVar(_)
        | mono::Expr::Constr(_)
        | mono::Expr::Char(_)
        | mono::Expr::Self_
        | mono::Expr::Int(_)
        | mono::Expr::AssocFnSelect(_)
        | mono::Expr::ConstrSelect(_) => {}

        mono::Expr::Variant(mono::VariantExpr { id: _, args }) => {
            for arg in args {
                visit_expr(&mut arg.node.node, closures, local_vars, free_vars);
            }
        }

        mono::Expr::FieldSelect(mono::FieldSelectExpr { object, field: _ }) => {
            visit_expr(&mut object.node, closures, local_vars, free_vars);
        }

        mono::Expr::MethodSelect(mono::MethodSelectExpr {
            object,
            method_ty_id: _,
            method_id: _,
            ty_args: _,
        }) => {
            visit_expr(&mut object.node, closures, local_vars, free_vars);
        }

        mono::Expr::Call(mono::CallExpr { fun, args }) => {
            visit_expr(&mut fun.node, closures, local_vars, free_vars);
            for mono::CallArg { name: _, expr } in args.iter_mut() {
                visit_expr(&mut expr.node, closures, local_vars, free_vars);
            }
        }

        mono::Expr::String(parts) => {
            for part in parts.iter_mut() {
                match part {
                    mono::StringPart::Str(_) => {}
                    mono::StringPart::Expr(expr) => {
                        visit_expr(&mut expr.node, closures, local_vars, free_vars);
                    }
                }
            }
        }

        mono::Expr::BinOp(mono::BinOpExpr { left, right, op: _ }) => {
            visit_expr(&mut left.node, closures, local_vars, free_vars);
            visit_expr(&mut right.node, closures, local_vars, free_vars);
        }

        mono::Expr::UnOp(mono::UnOpExpr { op: _, expr }) => {
            visit_expr(&mut expr.node, closures, local_vars, free_vars)
        }

        mono::Expr::Record(fields) => {
            for field in fields {
                visit_expr(&mut field.node.node, closures, local_vars, free_vars);
            }
        }

        mono::Expr::Return(l) => visit_expr(&mut l.node, closures, local_vars, free_vars),

        mono::Expr::Match(mono::MatchExpr { scrutinee, alts }) => {
            visit_expr(&mut scrutinee.node, closures, local_vars, free_vars);
            for mono::Alt {
                pattern,
                guard,
                rhs,
            } in alts
            {
                local_vars.enter();
                bind_pat_binders(&pattern.node, local_vars);
                if let Some(guard) = guard {
                    visit_expr(&mut guard.node, closures, local_vars, free_vars);
                }
                for stmt in rhs {
                    visit_stmt(&mut stmt.node, closures, local_vars, free_vars);
                }
                local_vars.exit();
            }
        }

        mono::Expr::If(mono::IfExpr {
            branches,
            else_branch,
        }) => {
            for (lhs, rhs) in branches.iter_mut() {
                visit_expr(&mut lhs.node, closures, local_vars, free_vars);
                local_vars.enter();
                for stmt in rhs {
                    visit_stmt(&mut stmt.node, closures, local_vars, free_vars);
                }
                local_vars.exit();
            }
            if let Some(stmts) = else_branch {
                local_vars.enter();
                for stmt in stmts {
                    visit_stmt(&mut stmt.node, closures, local_vars, free_vars);
                }
                local_vars.exit();
            }
        }
    }
}

fn bind_pat_binders(pat: &mono::Pat, local_vars: &mut ScopeSet<Id>) {
    match pat {
        mono::Pat::Var(var) | mono::Pat::StrPfx(_, var) => local_vars.insert(var.clone()),

        mono::Pat::Variant(mono::VariantPattern { constr: _, fields })
        | mono::Pat::Record(fields)
        | mono::Pat::Constr(mono::ConstrPattern {
            constr: _,
            fields,
            ty_args: _,
        }) => {
            for field in fields {
                bind_pat_binders(&field.node.node, local_vars);
            }
        }

        mono::Pat::Ignore | mono::Pat::Str(_) | mono::Pat::Char(_) => {}

        mono::Pat::Or(pat1, _) => {
            // Patterns bind same vars.
            bind_pat_binders(&pat1.node, local_vars);
        }
    }
}
