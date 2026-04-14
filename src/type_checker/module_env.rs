use crate::ast;
use crate::collections::*;
use crate::module::ModulePath;
use crate::module_loader::*;
use crate::name::Name;
use crate::type_checker::id::Id;

/// For each module in the program, generate the module environment that maps the names that can be
/// used in the module to their definitions.
pub fn generate_module_envs(pgm: &LoadedPgm) -> HashMap<ModulePath, HashMap<Name, Id>> {
    let mut envs: HashMap<ModulePath, HashMap<Name, Id>> = Default::default();

    // For each of the modules in the SCC, initialize envs with
    // (1) defined things
    // (2) imported things
    // We add defined things first, and don't allow imported things to shadow defined things.
    // (imported things silently ignored)

    // TODO: We currently allow importing the same name (with different definitions) from multiple
    // modules. We should raise an error *at the use site* when a name can be resolved to multiple
    // definitions.

    // NB. SCC graph is topologically sorted.
    for SccNode { modules, .. } in pgm.scc_graph.nodes.iter() {
        for module_path in modules.iter() {
            // (1) Locally defined things.
            {
                let mut env: HashMap<Name, Id> = Default::default();
                let module = pgm.modules.get(module_path).unwrap();
                for decl in module.decls.iter() {
                    match &decl.node {
                        ast::TopDecl::Type(ty_decl) => {
                            env.insert(
                                ty_decl.node.name.clone(),
                                Id::new(module_path, &ty_decl.node.name),
                            );
                        }

                        ast::TopDecl::Trait(trait_decl) => {
                            env.insert(
                                trait_decl.node.name.node.clone(),
                                Id::new(module_path, &trait_decl.node.name.node),
                            );
                        }

                        ast::TopDecl::Fun(fun_decl) => {
                            if fun_decl.node.parent_ty.is_none() {
                                env.insert(
                                    fun_decl.node.name.node.clone(),
                                    Id::new(module_path, &fun_decl.node.name.node),
                                );
                            }
                        }

                        ast::TopDecl::Import(_) | ast::TopDecl::Impl(_) => {}
                    }
                }
                let old = envs.insert(module_path.clone(), env);
                assert!(old.is_none());
            }
        }

        // (2) Add and propagate imports.
        let mut updated = true;
        while updated {
            updated = false;
            for module_path in modules.iter() {
                for module_import in pgm.dep_graph.get(module_path).unwrap() {
                    // Same as above: handle the harmless case of a module importing itself.
                    if &module_import.path == module_path {
                        continue;
                    }
                    let imported_module_env = envs.remove(&module_import.path).unwrap();
                    let mut importing_module_env = envs.remove(module_path).unwrap();
                    updated |= import(
                        &mut importing_module_env,
                        &imported_module_env,
                        module_import.filter.as_ref(),
                    );
                    envs.insert(module_import.path.clone(), imported_module_env);
                    envs.insert(module_path.clone(), importing_module_env);
                }
            }
        }
    }

    envs
}

/// Returns whether a new name was imported.
///
/// `filter`: `None` means import everything. `Some(map)` means import only the names in the map,
/// using the map values as local names (supports renaming).
fn import(
    importing_env: &mut HashMap<Name, Id>,
    imported_env: &HashMap<Name, Id>,
    filter: Option<&HashMap<Name, Name>>,
) -> bool {
    let mut updated = false;
    for (imported_name, imported_id) in imported_env.iter() {
        if imported_name.starts_with('_') {
            // Private definitions are not imported.
            continue;
        }
        let local_name = match filter {
            Some(filter) => match filter.get(imported_name) {
                Some(local_name) => local_name.clone(),
                None => continue,
            },
            None => imported_name.clone(),
        };
        if let std::collections::hash_map::Entry::Vacant(entry) = importing_env.entry(local_name) {
            entry.insert(imported_id.clone());
            updated = true;
        }
    }
    updated
}
