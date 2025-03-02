use crate::ast::{self, Id};
use crate::collections::{Map, ScopeSet, Set};

#[derive(Debug)]
pub struct Closure {
    pub ast: ast::FnExpr,
    pub fvs: Map<Id, u32>,
}

pub fn collect_closures(pgm: &mut ast::Module) -> Vec<Closure> {
    let mut closures: Vec<Closure> = vec![];
    let top_vars: Set<Id> = collect_top_vars(pgm);

    for decl in pgm.iter_mut() {
        match &mut decl.node {
            ast::TopDecl::Fun(fun_decl) => {
                visit_fun_decl(&mut fun_decl.node, &mut closures, &top_vars)
            }

            ast::TopDecl::Trait(ast::L {
                loc: _,
                node:
                    ast::TraitDecl {
                        name: _,
                        ty: _,
                        items,
                    },
            }) => {
                for item in items {
                    match &mut item.node {
                        ast::TraitDeclItem::AssocTy(_) => {}
                        ast::TraitDeclItem::Fun(fun_decl) => {
                            visit_fun_decl(fun_decl, &mut closures, &top_vars)
                        }
                    }
                }
            }

            ast::TopDecl::Impl(ast::L {
                loc: _,
                node:
                    ast::ImplDecl {
                        context: _,
                        trait_: _,
                        ty: _,
                        items,
                    },
            }) => {
                for item in items.iter_mut() {
                    match &mut item.node {
                        ast::ImplDeclItem::AssocTy(_) => {}
                        ast::ImplDeclItem::Fun(fun_decl) => {
                            visit_fun_decl(fun_decl, &mut closures, &top_vars)
                        }
                    }
                }
            }

            ast::TopDecl::Type(_) | ast::TopDecl::Import(_) => {}
        }
    }

    closures
}

fn visit_fun_decl(decl: &mut ast::FunDecl, closures: &mut Vec<Closure>, top_vars: &Set<Id>) {
    let mut local_vars: ScopeSet<Id> = Default::default();

    for (param, _) in &decl.sig.params {
        local_vars.insert(param.clone());
    }

    if let Some(body) = &mut decl.body {
        for stmt in body.iter_mut() {
            visit_stmt(
                &mut stmt.node,
                closures,
                top_vars,
                &mut local_vars,
                &mut Default::default(),
            );
        }
    }
}

fn visit_stmt(
    decl: &mut ast::Stmt,
    closures: &mut Vec<Closure>,
    top_vars: &Set<Id>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, u32>,
) {
    match decl {
        ast::Stmt::Let(ast::LetStmt { lhs, ty: _, rhs }) => {
            bind_pat_binders(&lhs.node, local_vars);
            visit_expr(&mut rhs.node, closures, top_vars, local_vars, free_vars);
        }

        ast::Stmt::Assign(ast::AssignStmt { lhs, rhs, op: _ }) => {
            visit_expr(&mut lhs.node, closures, top_vars, local_vars, free_vars);
            visit_expr(&mut rhs.node, closures, top_vars, local_vars, free_vars);
        }

        ast::Stmt::Expr(expr) => {
            visit_expr(&mut expr.node, closures, top_vars, local_vars, free_vars);
        }

        ast::Stmt::For(ast::ForStmt {
            label: _,
            pat,
            ty: _,
            expr,
            expr_ty: _,
            body,
        }) => {
            visit_expr(&mut expr.node, closures, top_vars, local_vars, free_vars);
            local_vars.enter();
            bind_pat_binders(&pat.node, local_vars);
            for stmt in body {
                visit_stmt(&mut stmt.node, closures, top_vars, local_vars, free_vars);
            }
            local_vars.exit();
        }

        ast::Stmt::While(ast::WhileStmt {
            label: _,
            cond,
            body,
        }) => {
            visit_expr(&mut cond.node, closures, top_vars, local_vars, free_vars);
            local_vars.enter();
            for stmt in body.iter_mut() {
                visit_stmt(&mut stmt.node, closures, top_vars, local_vars, free_vars);
            }
            local_vars.exit();
        }

        ast::Stmt::WhileLet(ast::WhileLetStmt {
            label: _,
            pat: _,
            cond,
            body,
        }) => {
            local_vars.enter();
            visit_expr(&mut cond.node, closures, top_vars, local_vars, free_vars);
            local_vars.exit();

            local_vars.enter();
            for stmt in body.iter_mut() {
                visit_stmt(&mut stmt.node, closures, top_vars, local_vars, free_vars);
            }
            local_vars.exit();
        }

        ast::Stmt::Break { .. } | ast::Stmt::Continue { .. } => {}
    }
}

fn visit_expr(
    expr: &mut ast::Expr,
    closures: &mut Vec<Closure>,
    top_vars: &Set<Id>,
    local_vars: &mut ScopeSet<Id>,
    free_vars: &mut Map<Id, u32>,
) {
    match expr {
        //------------------------------------------------------------------------------------------
        ast::Expr::Fn(ast::FnExpr { sig, body, idx }) => {
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
                    top_vars,
                    &mut fn_local_vars,
                    &mut fn_free_vars,
                );
            }

            let closure_idx = closures.len() as u32;
            *idx = closure_idx;
            closures.push(Closure {
                ast: ast::FnExpr {
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

        ast::Expr::Var(ast::VarExpr { id, ty_args: _ }) => {
            if !top_vars.contains(id) && !local_vars.is_bound(id) {
                let idx = free_vars.len() as u32;
                free_vars.insert(id.clone(), idx);
            }
        }

        //------------------------------------------------------------------------------------------
        ast::Expr::Constr(_)
        | ast::Expr::Char(_)
        | ast::Expr::Self_
        | ast::Expr::Int(_)
        | ast::Expr::AssocFnSelect(_)
        | ast::Expr::ConstrSelect(_) => {}

        ast::Expr::Variant(ast::VariantExpr { id: _, args }) => {
            for arg in args {
                visit_expr(
                    &mut arg.node.node,
                    closures,
                    top_vars,
                    local_vars,
                    free_vars,
                );
            }
        }

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field: _ }) => {
            visit_expr(&mut object.node, closures, top_vars, local_vars, free_vars);
        }

        ast::Expr::MethodSelect(ast::MethodSelectExpr {
            object,
            object_ty: _,
            method: _,
            ty_args: _,
        }) => {
            visit_expr(&mut object.node, closures, top_vars, local_vars, free_vars);
        }

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            visit_expr(&mut fun.node, closures, top_vars, local_vars, free_vars);
            for ast::CallArg { name: _, expr } in args.iter_mut() {
                visit_expr(&mut expr.node, closures, top_vars, local_vars, free_vars);
            }
        }

        ast::Expr::String(parts) => {
            for part in parts.iter_mut() {
                match part {
                    crate::interpolation::StringPart::Str(_) => {}
                    crate::interpolation::StringPart::Expr(expr) => {
                        visit_expr(&mut expr.node, closures, top_vars, local_vars, free_vars);
                    }
                }
            }
        }

        ast::Expr::BinOp(ast::BinOpExpr { left, right, op: _ }) => {
            visit_expr(&mut left.node, closures, top_vars, local_vars, free_vars);
            visit_expr(&mut right.node, closures, top_vars, local_vars, free_vars);
        }

        ast::Expr::UnOp(ast::UnOpExpr { op: _, expr }) => {
            visit_expr(&mut expr.node, closures, top_vars, local_vars, free_vars)
        }

        ast::Expr::Record(fields) => {
            for field in fields {
                visit_expr(
                    &mut field.node.node,
                    closures,
                    top_vars,
                    local_vars,
                    free_vars,
                );
            }
        }

        ast::Expr::Return(l) => visit_expr(&mut l.node, closures, top_vars, local_vars, free_vars),

        ast::Expr::Match(ast::MatchExpr { scrutinee, alts }) => {
            visit_expr(
                &mut scrutinee.node,
                closures,
                top_vars,
                local_vars,
                free_vars,
            );
            for ast::Alt {
                pattern,
                guard,
                rhs,
            } in alts
            {
                local_vars.enter();
                bind_pat_binders(&pattern.node, local_vars);
                if let Some(guard) = guard {
                    visit_expr(&mut guard.node, closures, top_vars, local_vars, free_vars);
                }
                for stmt in rhs {
                    visit_stmt(&mut stmt.node, closures, top_vars, local_vars, free_vars);
                }
                local_vars.exit();
            }
        }

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            for (lhs, rhs) in branches.iter_mut() {
                visit_expr(&mut lhs.node, closures, top_vars, local_vars, free_vars);
                local_vars.enter();
                for stmt in rhs {
                    visit_stmt(&mut stmt.node, closures, top_vars, local_vars, free_vars);
                }
                local_vars.exit();
            }
            if let Some(stmts) = else_branch {
                local_vars.enter();
                for stmt in stmts {
                    visit_stmt(&mut stmt.node, closures, top_vars, local_vars, free_vars);
                }
                local_vars.exit();
            }
        }
    }
}

fn collect_top_vars(pgm: &ast::Module) -> Set<Id> {
    let mut vars: Set<Id> = Default::default();

    for decl in pgm {
        match &decl.node {
            ast::TopDecl::Fun(fun_decl) => {
                vars.insert(fun_decl.node.name.node.clone());
            }

            ast::TopDecl::Trait(_) | ast::TopDecl::Impl(_) | ast::TopDecl::Type(_) => {}

            ast::TopDecl::Import(_) => panic!(),
        }
    }

    vars
}

fn bind_pat_binders(pat: &ast::Pat, local_vars: &mut ScopeSet<Id>) {
    match pat {
        ast::Pat::Var(var) | ast::Pat::StrPfx(_, var) => local_vars.insert(var.clone()),

        ast::Pat::Variant(ast::VariantPattern { constr: _, fields })
        | ast::Pat::Record(fields)
        | ast::Pat::Constr(ast::ConstrPattern {
            constr: _,
            fields,
            ty_args: _,
        }) => {
            for field in fields {
                bind_pat_binders(&field.node.node, local_vars);
            }
        }

        ast::Pat::Ignore | ast::Pat::Str(_) | ast::Pat::Char(_) => {}

        ast::Pat::Or(pat1, _) => {
            // Patterns bind same vars.
            bind_pat_binders(&pat1.node, local_vars);
        }
    }
}
