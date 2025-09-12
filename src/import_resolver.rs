use crate::ast::{self, Id};
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
pub fn resolve_imports(module: ast::Module, import_prelude: bool) -> ast::Module {
    let mut new_module: Vec<ast::L<ast::TopDecl>> = vec![];
    let mut imported_modules: Set<Vec<Id>> = Default::default();

    resolve_imports_(module, &mut new_module, &mut imported_modules);

    // Import Prelude if it's not already imported.
    let prelude_path = vec![FIR.clone(), PRELUDE.clone()];
    if import_prelude && !imported_modules.contains(&prelude_path) {
        let prelude_path_buf = module_path(&prelude_path);
        let prelude_module = crate::parse_file(&prelude_path_buf, &PRELUDE);
        imported_modules.insert(prelude_path);
        resolve_imports_(prelude_module, &mut new_module, &mut imported_modules);
    }

    new_module
}

static FIR: Id = SmolStr::new_static("Fir");
static PRELUDE: Id = SmolStr::new_static("Prelude");

type Path = Vec<Id>;

fn resolve_imports_(
    module: ast::Module,
    new_module: &mut ast::Module,
    imported_modules: &mut Set<Path>,
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

                imported_modules.insert(path.clone());

                let imported_module_path = module_path(path);
                let imported_module =
                    crate::parse_file(&imported_module_path, path.last().unwrap());
                resolve_imports_(imported_module, new_module, imported_modules);
            }
        }
    }
}

fn module_path(import_path: &[Id]) -> PathBuf {
    let mut path = PathBuf::new();
    for p in import_path.iter() {
        path.push(p.as_str());
    }
    path.set_extension("fir");
    path
}
