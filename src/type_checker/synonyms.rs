use crate::type_checker::*;

/// Resolve a type synonym by converting its RHS. If the RHS references another synonym, resolve
/// that one first (recursively). Detects cycles via the `resolving` set.
pub(super) fn resolve_synonym(
    syn_id: &Id,
    synonym_asts: &HashMap<Id, (&ModulePath, &[ast::TypeParam], &[Kind], &ast::L<ast::Type>)>,
    resolving: &mut HashSet<Id>,
    tys: &mut TyMap,
    module_envs: &HashMap<ModulePath, ModuleEnv>,
) {
    let (module_path, type_params, type_param_kinds, rhs_ty) = synonym_asts.get(syn_id).unwrap();
    let module_env = module_envs.get(*module_path).unwrap();

    // Already resolved in a previous call.
    if tys.has_con(syn_id) {
        return;
    }

    if !resolving.insert(syn_id.clone()) {
        let cycle: Vec<String> = resolving.iter().map(|id| id.to_string()).collect();
        panic!("Type synonym cycle detected: {}", cycle.join(", "));
    }

    // Resolve synonyms in the RHS.
    resolve_synonym_deps(
        &rhs_ty.node,
        module_env,
        synonym_asts,
        resolving,
        tys,
        module_envs,
    );

    // Bind type params as QVars so they're available when converting the RHS.
    tys.enter_scope();
    for (param, kind) in type_params.iter().zip(type_param_kinds.iter()) {
        tys.insert_var(
            param.name.node.clone(),
            Ty::QVar(param.name.node.clone(), *kind),
        );
    }
    let converted = convert_ast_ty(tys, module_env, &rhs_ty.node, &rhs_ty.loc);
    tys.exit_scope();

    tys.insert_con(
        syn_id.clone(),
        TyCon {
            id: syn_id.clone(),
            ty_params: type_params
                .iter()
                .zip(type_param_kinds.iter())
                .map(|(p, k)| (p.name.node.clone(), *k))
                .collect(),
            details: TyConDetails::Synonym(converted),
        },
    );

    resolving.remove(syn_id);
}

/// Recursively resolve any synonym dependencies in an AST type.
fn resolve_synonym_deps(
    ty: &ast::Type,
    module_env: &ModuleEnv,
    synonym_asts: &HashMap<Id, (&ModulePath, &[ast::TypeParam], &[Kind], &ast::L<ast::Type>)>,
    resolving: &mut HashSet<Id>,
    tys: &mut TyMap,
    module_envs: &HashMap<ModulePath, ModuleEnv>,
) {
    match ty {
        ast::Type::Named(ast::NamedType {
            mod_prefix,
            name,
            args,
        }) => {
            if let Some(id) = module_env.get_with_path(name, mod_prefix)
                && synonym_asts.contains_key(id)
            {
                resolve_synonym(id, synonym_asts, resolving, tys, module_envs);
            }
            for arg in args {
                resolve_synonym_deps(
                    &arg.node,
                    module_env,
                    synonym_asts,
                    resolving,
                    tys,
                    module_envs,
                );
            }
        }
        ast::Type::Var(_) => {}
        ast::Type::Record { fields, .. } => {
            for (_, field_ty) in fields {
                resolve_synonym_deps(
                    field_ty,
                    module_env,
                    synonym_asts,
                    resolving,
                    tys,
                    module_envs,
                );
            }
        }
        ast::Type::Variant { alts, .. } => {
            for alt in alts {
                for arg in &alt.args {
                    resolve_synonym_deps(
                        &arg.node,
                        module_env,
                        synonym_asts,
                        resolving,
                        tys,
                        module_envs,
                    );
                }
            }
        }
        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => {
            for arg in args {
                resolve_synonym_deps(
                    &arg.node,
                    module_env,
                    synonym_asts,
                    resolving,
                    tys,
                    module_envs,
                );
            }
            if let Some(ret) = ret {
                resolve_synonym_deps(
                    &ret.node,
                    module_env,
                    synonym_asts,
                    resolving,
                    tys,
                    module_envs,
                );
            }
            if let Some(exn) = exceptions {
                resolve_synonym_deps(
                    &exn.node,
                    module_env,
                    synonym_asts,
                    resolving,
                    tys,
                    module_envs,
                );
            }
        }
        ast::Type::AssocTySelect { ty: inner, .. } => {
            resolve_synonym_deps(
                &inner.node,
                module_env,
                synonym_asts,
                resolving,
                tys,
                module_envs,
            );
        }
    }
}
