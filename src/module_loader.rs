use crate::ast;
use crate::collections::*;
use crate::module::ModulePath;

use std::path::Path;

use smol_str::SmolStr;

pub struct LoadedProgram {
    pub modules: HashMap<ModulePath, ast::Module>,

    #[allow(dead_code)]
    pub entry: ModulePath,
}

pub fn load(entry_file: &Path, import_prelude: bool) -> LoadedProgram {
    let entry = ModulePath::from_file_path(entry_file);
    let mut work: Vec<ModulePath> = vec![entry.clone()];
    let mut modules: HashMap<ModulePath, ast::Module> = HashMap::default();
    modules.insert(entry.clone(), ast::Module::empty());

    if import_prelude {
        let prelude_path = ModulePath::new(vec![
            SmolStr::new_static("Fir"),
            SmolStr::new_static("Prelude"),
        ]);
        work.push(prelude_path.clone());
        modules.insert(prelude_path.clone(), ast::Module::empty());
    }

    while let Some(module_path) = work.pop() {
        let file_path = module_path.to_file_path();
        let display_name = module_path.to_string();
        let module = crate::parse_file(&file_path, &display_name);

        for decl in &module.decls {
            if let ast::TopDecl::Import(import) = &decl.node {
                for item in &import.node.items {
                    if !modules.contains_key(&item.path) {
                        modules.insert(item.path.clone(), ast::Module::empty());
                        work.push(item.path.clone());
                    }
                }
            }
        }

        let old = modules.insert(module_path, module);
        debug_assert!(old.unwrap().decls.is_empty());
    }

    LoadedProgram { modules, entry }
}

impl LoadedProgram {
    pub fn merge(self) -> ast::Module {
        let mut merged_module: ast::Module = ast::Module::empty();

        for module in self.modules.into_values() {
            for decl in module.decls {
                match &decl.node {
                    ast::TopDecl::Type(_)
                    | ast::TopDecl::Fun(_)
                    | ast::TopDecl::Trait(_)
                    | ast::TopDecl::Impl(_) => merged_module.decls.push(decl),

                    ast::TopDecl::Import(_) => {}
                }
            }
        }

        merged_module
    }
}
