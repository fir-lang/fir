use crate::ast;
use crate::collections::Set;

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
    fir_root: &str,
    module_root: &str,
    module: ast::Module,
    import_prelude: bool,
) -> ast::Module {
    let mut new_module: Vec<ast::L<ast::TopDecl>> = vec![];
    let mut imported_modules: Set<Vec<SmolStr>> = Default::default();

    let fir_root = fir_lib_root(fir_root);
    let fir_root_str = fir_root.to_str().unwrap();

    resolve_imports_(
        fir_root_str,
        module_root,
        module,
        &mut new_module,
        &mut imported_modules,
    );

    // Import Prelude if it's not already imported.
    let prelude_path = prelude_module_path();
    if import_prelude && !imported_modules.contains(&prelude_path) {
        let prelude_path_buf = module_path(fir_root.to_str().unwrap(), &PRELUDE);
        let prelude_module = crate::parse_file(&prelude_path_buf, &PRELUDE);
        imported_modules.insert(prelude_path);
        resolve_imports_(
            fir_root_str,
            fir_root_str,
            prelude_module,
            &mut new_module,
            &mut imported_modules,
        );
    }

    new_module
}

static FIR: SmolStr = SmolStr::new_static("Fir");
static PRELUDE: SmolStr = SmolStr::new_static("Prelude");

fn prelude_module_path() -> Vec<SmolStr> {
    vec![FIR.clone(), PRELUDE.clone()]
}

fn resolve_imports_(
    fir_lib_root: &str,
    module_root: &str,
    module: ast::Module,
    new_module: &mut ast::Module,
    imported_modules: &mut Set<Vec<SmolStr>>,
) {
    for decl in module {
        match &decl.node {
            ast::TopDecl::Type(_)
            | ast::TopDecl::Fun(_)
            | ast::TopDecl::Trait(_)
            | ast::TopDecl::Impl(_) => new_module.push(decl),
            ast::TopDecl::Import(import) => {
                let path = &import.node.path;

                if imported_modules.contains(path) {
                    continue;
                }

                let root = if path.len() == 2 && path[0] == "Fir" {
                    fir_lib_root
                } else if path.len() == 1 {
                    module_root
                } else {
                    panic!("Unsupported import path: {:?}", path);
                };

                let imported_module = path.last().unwrap();
                imported_modules.insert(path.clone());

                let imported_module_path = module_path(root, imported_module);
                let imported_module = crate::parse_file(&imported_module_path, imported_module);
                resolve_imports_(
                    fir_lib_root,
                    module_root,
                    imported_module,
                    new_module,
                    imported_modules,
                );
            }
        }
    }
}

fn module_path(root: &str, module: &SmolStr) -> PathBuf {
    let mut path = PathBuf::new();
    path.push(root);
    path.push(module.as_str());
    path.set_extension("fir");
    path
}

fn fir_lib_root(fir_root: &str) -> PathBuf {
    let mut path = PathBuf::new();
    path.push(fir_root);
    path.push("lib");
    path
}
