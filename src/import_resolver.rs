use crate::ast::{self, Id};
use crate::collections::{Map, Set};

use std::path::PathBuf;

use smol_str::SmolStr;

/// Replaces import declarations with the parsed ASTs of the imported modules.
///
/// A simple import resolver that will do until we implement a proper module system.
///
/// Handles modules imported multiple times transitively.
///
/// The returned module won't have any import declarations.
///
/// Imports `Fir.Prelude` always. Any other import path needs to have one component and will be
/// resolved to a file at the root.
pub fn resolve_imports(
    import_paths: &Map<String, String>,
    module_root: &str,
    module: ast::Module,
    import_prelude: bool,
    print_tokens: bool,
) -> ast::Module {
    let mut new_module: Vec<ast::L<ast::TopDecl>> = vec![];
    let mut imported_modules: Set<Vec<Id>> = Default::default();

    let fir_root = import_paths.get("Fir").unwrap();

    resolve_imports_(
        import_paths,
        module_root,
        module_root,
        module,
        &mut new_module,
        &mut imported_modules,
        print_tokens,
    );

    // Import Prelude if it's not already imported.
    let prelude_path = vec![FIR.clone(), PRELUDE.clone()];
    if import_prelude && !imported_modules.contains(&prelude_path) {
        let prelude_path_buf = module_path(fir_root, &PRELUDE);
        let prelude_module = crate::parse_file(&prelude_path_buf, &PRELUDE, print_tokens);
        imported_modules.insert(prelude_path);
        resolve_imports_(
            import_paths,
            module_root,
            fir_root,
            prelude_module,
            &mut new_module,
            &mut imported_modules,
            print_tokens,
        );
    }

    new_module
}

static FIR: Id = SmolStr::new_static("Fir");
static PRELUDE: Id = SmolStr::new_static("Prelude");

type Path = Vec<Id>;

fn resolve_imports_(
    import_paths: &Map<String, String>,
    main_module_root: &str,
    module_root: &str,
    module: ast::Module,
    new_module: &mut ast::Module,
    imported_modules: &mut Set<Path>,
    print_tokens: bool,
) {
    for decl in module {
        match &decl.node {
            ast::TopDecl::Type(_)
            | ast::TopDecl::Fun(_)
            | ast::TopDecl::Trait(_)
            | ast::TopDecl::Impl(_) => new_module.push(decl),
            ast::TopDecl::Import(import) => {
                let path = &import.node.path;

                assert!(
                    path.len() <= 2,
                    "We don't allow directories in import paths currently. Invalid path: {}",
                    path.join(".")
                );

                let full_path = if path.len() == 2 {
                    path.clone()
                } else {
                    // Find what the module at this root is called.
                    //
                    // This is quite hacky.. When the main module imports another in the same
                    // directory
                    //
                    // - the path will only the module name, AND
                    //
                    // - the `module_root` will be the directory of the main module, AND
                    //
                    // - `import_paths` won't have an entry for the module as we don't give a name
                    //   to the directory of the main module.

                    if module_root == main_module_root {
                        vec![path[0].clone()]
                    } else {
                        let pkg_name = import_paths
                            .iter()
                            .find(|(_pkg_name, pkg_path)| *pkg_path == module_root)
                            .unwrap_or_else(|| {
                                panic!(
                                    "Can't find package name for modules at {}. \
                                     Specify the path's package name with `-i<package name>={}",
                                    module_root, module_root
                                )
                            })
                            .0;
                        vec![SmolStr::new(pkg_name), path[0].clone()]
                    }
                };

                if imported_modules.contains(&full_path) {
                    continue;
                }

                let root = if path.len() == 2 {
                    match import_paths.get(path[0].as_str()) {
                        Some(root) => root,
                        None => panic!("Path {} is not in import paths", path[0]),
                    }
                } else {
                    module_root
                };

                imported_modules.insert(full_path.clone());

                let imported_module = path.last().unwrap();
                let imported_module_path = module_path(root, imported_module);
                let imported_module =
                    crate::parse_file(&imported_module_path, imported_module, print_tokens);
                resolve_imports_(
                    import_paths,
                    main_module_root,
                    root,
                    imported_module,
                    new_module,
                    imported_modules,
                    print_tokens,
                );
            }
        }
    }
}

fn module_path(root: &str, module: &Id) -> PathBuf {
    let mut path = PathBuf::new();
    path.push(root);
    path.push(module.as_str());
    path.set_extension("fir");
    path
}
