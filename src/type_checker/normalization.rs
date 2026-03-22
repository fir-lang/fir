use crate::ast::{self, Id};
use crate::collections::{OrderMap, ScopeMap};
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
                    .deep_normalize(cons, trait_env, var_gen, &[]),
            );
            ty_args
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen, &[]))
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
                    .deep_normalize(cons, trait_env, var_gen, &[]),
            );
            ty_args
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen, &[]));
        }

        ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
            ty_args,
            inferred_ty,
            ..
        }) => {
            *inferred_ty = Some(inferred_ty.as_ref().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
            ty_args
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen, &[]))
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
                    .deep_normalize(cons, trait_env, var_gen, &[]),
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
            *inferred_ty = Some(inferred_ty.as_ref().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
            ty_args
                .iter_mut()
                .for_each(|ty| *ty = ty.deep_normalize(cons, trait_env, var_gen, &[]));
            normalize_expr(&mut object.node, &object.loc, cons, trait_env, var_gen)
        }

        ast::Expr::Call(ast::CallExpr {
            fun,
            args,
            inferred_ty,
        }) => {
            *inferred_ty = Some(inferred_ty.as_ref().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
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
            *inferred_ty = Some(inferred_ty.as_ref().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
            normalize_expr(&mut expr.node, &expr.loc, cons, trait_env, var_gen);
        }

        ast::Expr::Match(ast::MatchExpr {
            scrutinee,
            alts,
            inferred_ty,
        }) => {
            *inferred_ty = Some(inferred_ty.as_ref().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
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
            *inferred_ty = Some(inferred_ty.as_ref().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
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
            *inferred_ty = Some(inferred_ty.as_ref().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
            for stmt in body {
                normalize_stmt(&mut stmt.node, &stmt.loc, cons, trait_env, var_gen);
            }
        }

        ast::Expr::Is(ast::IsExpr { expr, pat }) => {
            normalize_expr(&mut expr.node, &expr.loc, cons, trait_env, var_gen);
            normalize_pat(&mut pat.node, cons, trait_env, var_gen);
        }

        ast::Expr::Do(ast::DoExpr { stmts, inferred_ty }) => {
            *inferred_ty = Some(inferred_ty.as_ref().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
            for stmt in stmts {
                normalize_stmt(&mut stmt.node, &stmt.loc, cons, trait_env, var_gen);
            }
        }

        ast::Expr::Seq { .. } => panic!("Seq expr should've been desugared"),

        ast::Expr::Record(ast::RecordExpr {
            fields,
            inferred_ty,
        }) => {
            *inferred_ty = Some(inferred_ty.as_mut().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
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
            *inferred_ty = Some(inferred_ty.as_mut().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
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
                    .deep_normalize(cons, trait_env, var_gen, &[]),
            );
            if let Some(ty) = refined {
                *ty = ty.deep_normalize(cons, trait_env, var_gen, &[]);
            }
        }

        ast::Pat::Ignore | ast::Pat::Str(_) | ast::Pat::Char(_) => {}

        ast::Pat::Con(ast::ConPat {
            con:
                ast::Con {
                    ty_args,
                    inferred_ty,
                    ..
                },
            fields,
            ignore_rest: _,
        }) => {
            *inferred_ty = Some(inferred_ty.as_ref().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
            for field in fields {
                normalize_pat(&mut field.node.node, cons, trait_env, var_gen);
            }
            for ty_arg in ty_args {
                *ty_arg = ty_arg.deep_normalize(cons, trait_env, var_gen, &[]);
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
            *inferred_ty = Some(inferred_ty.as_mut().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
            fields.iter_mut().for_each(|ast::Named { name: _, node }| {
                normalize_pat(&mut node.node, cons, trait_env, var_gen)
            });
        }

        ast::Pat::Variant(ast::VariantPat {
            pat,
            inferred_ty,
            inferred_pat_ty,
        }) => {
            *inferred_ty = Some(inferred_ty.as_mut().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
            *inferred_pat_ty = Some(inferred_pat_ty.as_mut().unwrap().deep_normalize(
                cons,
                trait_env,
                var_gen,
                &[],
            ));
            normalize_pat(&mut pat.node, cons, trait_env, var_gen);
        }
    }
}

/// Expand type synonym references in all `ast::Type` nodes in the module. This must run after type
/// checking and before monomorphization.
pub(super) fn expand_type_synonyms(module: &mut ast::Module) {
    // Collect top-level synonyms.
    let mut synonyms: OrderMap<Id, ast::Type> = Default::default();
    for decl in module.iter() {
        if let ast::TopDecl::Type(ty_decl) = &decl.node
            && let Some(ast::TypeDeclRhs::Synonym(rhs)) = &ty_decl.node.rhs
        {
            synonyms.insert(ty_decl.node.name.clone(), rhs.node.clone());
        }
    }

    for decl in module.iter_mut() {
        match &mut decl.node {
            ast::TopDecl::Type(ty_decl) => {
                expand_synonyms_in_type_decl(&mut ty_decl.node, &synonyms);
            }

            ast::TopDecl::Fun(fun) => {
                expand_synonyms_in_fun(&mut fun.node, &synonyms);
            }

            ast::TopDecl::Trait(trait_decl) => {
                // Build scoped synonyms: trait associated types map to AssocTySelect.
                let mut scoped = synonyms.clone();
                for item in &trait_decl.node.items {
                    if let ast::TraitDeclItem::Type(assoc_ty) = item {
                        let trait_ty = ast::Type::Named(ast::NamedType {
                            name: trait_decl.node.name.node.clone(),
                            args: trait_decl
                                .node
                                .type_params
                                .iter()
                                .map(|p| p.map_as_ref(|p| ast::Type::Var(p.clone())))
                                .collect(),
                        });
                        scoped.insert(
                            assoc_ty.node.clone(),
                            ast::Type::AssocTySelect {
                                ty: assoc_ty.set_node(Box::new(trait_ty)),
                                assoc_ty: assoc_ty.node.clone(),
                            },
                        );
                    }
                }

                for item in &mut trait_decl.node.items {
                    if let ast::TraitDeclItem::Fun(fun) = item {
                        expand_synonyms_in_fun(&mut fun.node, &scoped);
                    }
                }
            }

            ast::TopDecl::Impl(impl_decl) => {
                // Build scoped synonyms: impl associated type assignments.
                let mut scoped = synonyms.clone();
                for item in &impl_decl.node.items {
                    if let ast::ImplDeclItem::Type { assoc_ty, rhs } = item {
                        // First expand any synonyms in the RHS itself.
                        let mut rhs_expanded = rhs.node.clone();
                        expand_synonyms_in_ty(&mut rhs_expanded, &synonyms);
                        scoped.insert(assoc_ty.node.clone(), rhs_expanded);
                    }
                }

                for item in &mut impl_decl.node.items {
                    match item {
                        ast::ImplDeclItem::Type { assoc_ty: _, rhs } => {
                            expand_synonyms_in_ty(&mut rhs.node, &synonyms);
                        }
                        ast::ImplDeclItem::Fun(fun) => {
                            expand_synonyms_in_fun(&mut fun.node, &scoped);
                        }
                    }
                }
            }

            ast::TopDecl::Import(_) => {}
        }
    }
}

fn expand_synonyms_in_type_decl(decl: &mut ast::TypeDecl, synonyms: &OrderMap<Id, ast::Type>) {
    match &mut decl.rhs {
        Some(ast::TypeDeclRhs::Sum(cons)) => {
            for con in cons {
                expand_synonyms_in_fields(&mut con.fields, synonyms);
            }
        }
        Some(ast::TypeDeclRhs::Product(fields)) => {
            expand_synonyms_in_fields(fields, synonyms);
        }
        Some(ast::TypeDeclRhs::Synonym(rhs)) => {
            expand_synonyms_in_ty(&mut rhs.node, synonyms);
        }
        None => {}
    }
}

fn expand_synonyms_in_fields(fields: &mut ast::ConFields, synonyms: &OrderMap<Id, ast::Type>) {
    match fields {
        ast::ConFields::Empty => {}
        ast::ConFields::Named(fields) => {
            for (_, ty) in fields {
                expand_synonyms_in_ty(&mut ty.node, synonyms);
            }
        }
        ast::ConFields::Unnamed(fields) => {
            for ty in fields {
                expand_synonyms_in_ty(&mut ty.node, synonyms);
            }
        }
    }
}

fn expand_synonyms_in_fun(fun: &mut ast::FunDecl, synonyms: &OrderMap<Id, ast::Type>) {
    expand_synonyms_in_sig(&mut fun.sig, synonyms);
}

fn expand_synonyms_in_sig(sig: &mut ast::FunSig, synonyms: &OrderMap<Id, ast::Type>) {
    if let ast::SelfParam::Explicit(ty) = &mut sig.self_ {
        expand_synonyms_in_ty(&mut ty.node, synonyms);
    }
    for (_, ty) in &mut sig.params {
        if let Some(ty) = ty {
            expand_synonyms_in_ty(&mut ty.node, synonyms);
        }
    }
    if let Some(ty) = &mut sig.return_ty {
        expand_synonyms_in_ty(&mut ty.node, synonyms);
    }
    if let Some(ty) = &mut sig.exceptions {
        expand_synonyms_in_ty(&mut ty.node, synonyms);
    }
}

fn expand_synonyms_in_ty(ty: &mut ast::Type, synonyms: &OrderMap<Id, ast::Type>) {
    match ty {
        ast::Type::Named(named) => {
            if named.args.is_empty()
                && let Some(expansion) = synonyms.get(&named.name)
            {
                *ty = expansion.clone();
                // Recursively expand in case the expansion contains more synonyms.
                expand_synonyms_in_ty(ty, synonyms);
                return;
            }
            for arg in &mut named.args {
                expand_synonyms_in_ty(&mut arg.node, synonyms);
            }
        }
        ast::Type::Var(_) => {}
        ast::Type::Record {
            fields,
            extension: _,
            is_row: _,
        } => {
            for (_, field_ty) in fields {
                expand_synonyms_in_ty(field_ty, synonyms);
            }
        }
        ast::Type::Variant {
            alts,
            extension: _,
            is_row: _,
        } => {
            for alt in alts {
                for arg in &mut alt.args {
                    expand_synonyms_in_ty(&mut arg.node, synonyms);
                }
            }
        }
        ast::Type::Fn(fn_ty) => {
            for arg in &mut fn_ty.args {
                expand_synonyms_in_ty(&mut arg.node, synonyms);
            }
            if let Some(ret) = &mut fn_ty.ret {
                expand_synonyms_in_ty(&mut ret.node, synonyms);
            }
            if let Some(exn) = &mut fn_ty.exceptions {
                expand_synonyms_in_ty(&mut exn.node, synonyms);
            }
        }
        ast::Type::AssocTySelect {
            ty: inner,
            assoc_ty: _,
        } => {
            expand_synonyms_in_ty(&mut inner.node, synonyms);
        }
    }
}
