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
#[derive(Debug, Default)]
pub(crate) struct ModuleEnv {
    /// Unprefixed names.
    names: NameMap,

    /// Prefixed names: prefix -> name -> id.
    prefixed: HashMap<Name, NameMap>,
}

/// Maps names to ids. Allows overriding imported names with defined names.
///
/// When a name is imported multiple times, collects all imported ids, to allow error reporting on
/// use.
#[derive(Debug, Default)]
struct NameMap {
    map: HashMap<Name, IdSet>,
}

#[derive(Debug)]
struct IdSet {
    // `HashSet<Id>` separate from a `defined` field to be able to provide an `iter` method that
    // yields all `Id`s.
    //
    // When `defined` is set, there must be only one element in the set.
    ids: HashSet<Id>,
    defined: bool,
}

impl NameMap {
    fn add_defined(&mut self, name: &Name, id: Id, loc: &ast::Loc) {
        match self.map.entry(name.clone()) {
            Entry::Occupied(mut entry) => {
                if entry.get().defined {
                    panic!("{}: {} defined multiple times", loc_display(loc), name);
                }
                entry.get_mut().ids.clear();
                entry.get_mut().ids.insert(id);
                entry.get_mut().defined = true;
            }
            Entry::Vacant(entry) => {
                entry.insert(IdSet {
                    ids: std::iter::once(id).collect(),
                    defined: true,
                });
            }
        }
    }

    /// Returns whether a new import is added.
    fn add_imported(&mut self, name: Name, id: Id) -> bool {
        match self.map.entry(name.clone()) {
            Entry::Occupied(mut entry) => {
                if entry.get().defined {
                    // Imported names don't shadow defined ones.
                    return false;
                }
                entry.get_mut().ids.insert(id)
            }
            Entry::Vacant(entry) => {
                entry.insert(IdSet {
                    ids: std::iter::once(id).collect(),
                    defined: false,
                });
                true
            }
        }
    }

    fn get(&self, name: &Name, loc: &ast::Loc) -> Id {
        match self.map.get(name) {
            None => {
                panic!("{}: Unbound name {}", loc_display(loc), name)
            }
            Some(id_set) => {
                debug_assert!(!id_set.ids.is_empty());
                if id_set.ids.len() == 1 {
                    id_set.ids.iter().next().cloned().unwrap()
                } else {
                    let mut msg = String::new();
                    msg.push_str(&format!(
                        "{}: Name {name} imported from multiple modules:\n",
                        loc_display(loc)
                    ));
                    for id in id_set.ids.iter() {
                        msg.push_str(&format!("- {}", id.module()));
                        msg.push('\n');
                    }
                    panic!("{msg}");
                }
            }
        }
    }

    fn iter(&self, module_path: &ModulePath) -> impl Iterator<Item = (&Name, &Id)> {
        self.map.iter().map(move |(name, id_set)| {
            if id_set.ids.len() == 1 {
                (name, id_set.ids.iter().next().unwrap())
            } else {
                let mut msg = format!("{module_path} exports multiple {name}s:\n");
                for id in &id_set.ids {
                    msg.push_str(&format!("{}/{}", id.module(), id.name()));
                    msg.push('\n');
                }
                panic!("{msg}")
            }
        })
    }
}

impl ModuleEnv {
    pub(crate) fn resolve(
        &self,
        name: &Name,
        mod_prefix: &Option<crate::module::ModulePath>,
        loc: &ast::Loc,
    ) -> Id {
        match mod_prefix {
            None => self.names.get(name, loc),
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
                    .get(&prefix)
                    .map(|name_map| name_map.get(name, loc))
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
                            env.names.add_defined(
                                &ty_decl.node.name,
                                Id::new(module_path, &ty_decl.node.name),
                                &decl.loc,
                            );
                        }

                        ast::TopDecl::Trait(trait_decl) => {
                            env.names.add_defined(
                                &trait_decl.node.name.node,
                                Id::new(module_path, &trait_decl.node.name.node),
                                &decl.loc,
                            );
                        }

                        ast::TopDecl::Fun(fun_decl) => {
                            if fun_decl.node.parent_ty.is_none() {
                                env.names.add_defined(
                                    &fun_decl.node.name.node,
                                    Id::new(module_path, &fun_decl.node.name.node),
                                    &decl.loc,
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
                        &module_import.path,
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
fn import(
    imported_module_path: &ModulePath,
    importing_env: &mut ModuleEnv,
    imported_env: &ModuleEnv,
    kind: &ImportKind,
) -> bool {
    let mut updated = false;
    match kind {
        ImportKind::Direct { filter } => {
            for (imported_name, imported_id) in imported_env.names.iter(imported_module_path) {
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
                updated |= importing_env
                    .names
                    .add_imported(local_name, imported_id.clone());
            }
        }

        ImportKind::Prefixed { prefix } => {
            let prefix_env = importing_env.prefixed.entry(prefix.clone()).or_default();
            for (imported_name, imported_id) in imported_env.names.iter(imported_module_path) {
                updated |= prefix_env.add_imported(imported_name.clone(), imported_id.clone());
            }
        }
    }
    updated
}
