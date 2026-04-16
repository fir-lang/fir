use crate::ast;
use crate::collections::*;
use crate::module::ModulePath;
use crate::module_loader::*;
use crate::name::Name;
use crate::type_checker::id::Id;
use crate::utils::loc_display;

/// Maps names visible in a module to their `Id`s.
///
/// Names can be either unprefixed (from direct/selective imports) or prefixed (from
/// `import [Foo as P]`, accessed as `P/name`).
#[derive(Debug, Clone, Default)]
pub(crate) struct ModuleEnv {
    /// Unprefixed names.
    names: HashMap<Name, Id>,

    /// Prefixed names: prefix -> name -> id.
    prefixed: HashMap<Name, HashMap<Name, Id>>,
}

impl ModuleEnv {
    pub(crate) fn resolve(
        &self,
        name: &Name,
        mod_prefix: &Option<crate::module::ModulePath>,
        loc: &ast::Loc,
    ) -> Id {
        match mod_prefix {
            None => self
                .names
                .get(name)
                .cloned()
                .unwrap_or_else(|| panic!("{}: Unbound name {}", loc_display(loc), name)),
            Some(path) => {
                let segments = path.segments();
                assert_eq!(
                    segments.len(),
                    1,
                    "{}: Multi-segment module paths not yet supported in name resolution",
                    loc_display(loc),
                );
                let prefix = Name::from(&segments[0]);
                self.prefixed
                    .get(&Name::from(&segments[0]))
                    .and_then(|prefix_map| prefix_map.get(name).cloned())
                    .unwrap_or_else(|| {
                        panic!("{}: Unbound name {}/{}", loc_display(loc), prefix, name)
                    })
            }
        }
    }
}

/// For each module in the program, generate the module environment that maps the names that can be
/// used in the module to their definitions.
pub(crate) fn generate_module_envs(pgm: &LoadedPgm) -> HashMap<ModulePath, ModuleEnv> {
    let mut envs: HashMap<ModulePath, ModuleEnv> = Default::default();

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
                let mut env = ModuleEnv::default();
                let module = pgm.modules.get(module_path).unwrap();
                for decl in module.decls.iter() {
                    match &decl.node {
                        ast::TopDecl::Type(ty_decl) => {
                            env.names.insert(
                                ty_decl.node.name.clone(),
                                Id::new(module_path, &ty_decl.node.name),
                            );
                        }

                        ast::TopDecl::Trait(trait_decl) => {
                            env.names.insert(
                                trait_decl.node.name.node.clone(),
                                Id::new(module_path, &trait_decl.node.name.node),
                            );
                        }

                        ast::TopDecl::Fun(fun_decl) => {
                            if fun_decl.node.parent_ty.is_none() {
                                env.names.insert(
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
                    // We'll remove the importing and imported envs below, so skip self imports
                    // where both envs are the same.
                    if &module_import.path == module_path {
                        continue;
                    }
                    let imported_module_env = envs.remove(&module_import.path).unwrap();
                    let mut importing_module_env = envs.remove(module_path).unwrap();
                    updated |= import(
                        &mut importing_module_env,
                        &imported_module_env,
                        &module_import.kind,
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
fn import(importing_env: &mut ModuleEnv, imported_env: &ModuleEnv, kind: &ImportKind) -> bool {
    let mut updated = false;
    match kind {
        ImportKind::Direct { filter } => {
            for (imported_name, imported_id) in imported_env.names.iter() {
                // Underscored names are not imported for direct use, but they can be used with a
                // prefix.
                if imported_name.starts_with('_') {
                    continue;
                }
                let local_name = match filter {
                    Some(filter) => match filter.get(imported_name) {
                        Some(local_name) => local_name.clone(),
                        None => continue,
                    },
                    None => imported_name.clone(),
                };
                if let std::collections::hash_map::Entry::Vacant(e) =
                    importing_env.names.entry(local_name)
                {
                    e.insert(imported_id.clone());
                    updated = true;
                }
            }
        }

        ImportKind::Prefixed { prefix } => {
            let prefix_env = importing_env.prefixed.entry(prefix.clone()).or_default();
            for (imported_name, imported_id) in imported_env.names.iter() {
                if !prefix_env.contains_key(imported_name) {
                    prefix_env.insert(imported_name.clone(), imported_id.clone());
                    updated = true;
                }
            }
        }
    }
    updated
}
