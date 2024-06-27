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
pub fn resolve_imports(root_path: &str, module: ast::Module) -> ast::Module {
    // The new module with all the imports removed, and declarations in the imported modules added.
    let mut new_module: Vec<ast::L<ast::TopDecl>> = vec![];
    resolve_imports_(root_path, module, &mut new_module, &mut Default::default());
    new_module
}

fn resolve_imports_(
    root_path: &str,
    module: ast::Module,
    new_module: &mut ast::Module,
    imported_modules: &mut Set<SmolStr>,
) {
    for decl in module {
        match &decl.thing {
            ast::TopDecl::Type(_) | ast::TopDecl::Fun(_) => new_module.push(decl),
            ast::TopDecl::Import(import) => {
                assert_eq!(import.thing.path.len(), 1, "TODO: Import with long path");
                let import_path = &import.thing.path[0];
                if imported_modules.contains(import_path) {
                    continue;
                }
                imported_modules.insert(import_path.clone());
                let imported_module_path = module_path(root_path, import_path);
                let imported_module = crate::parse_file(&imported_module_path, import_path);
                resolve_imports_(root_path, imported_module, new_module, imported_modules);
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
