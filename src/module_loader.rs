use crate::ast;
use crate::collections::*;
use crate::module::ModulePath;
use crate::utils::loc_display;

use std::path::Path;

use smol_str::SmolStr;

pub struct LoadedProgram {
    pub modules: HashMap<ModulePath, ast::Module>,

    #[allow(dead_code)]
    pub entry: ModulePath,
}

pub fn load(entry_file: &Path) -> LoadedProgram {
    let entry = ModulePath::from_file_path(entry_file);
    let mut work: Vec<ModulePath> = vec![entry.clone()];
    let mut modules: HashMap<ModulePath, ast::Module> = HashMap::default();
    modules.insert(entry.clone(), ast::Module::empty());

    let prelude_path = ModulePath::new(vec![
        SmolStr::new_static("Fir"),
        SmolStr::new_static("Prelude"),
    ]);

    while let Some(module_path) = work.pop() {
        let file_path = module_path.to_file_path();
        let display_name = module_path.to_string();
        let module = crate::parse_file(&file_path, &display_name);

        let mut implicit_prelude = true;

        for decl in &module.decls {
            if let ast::TopDecl::Import(import) = &decl.node {
                implicit_prelude &= !no_implicit_prelude(import);
                for item in &import.node.items {
                    if !modules.contains_key(&item.path) {
                        modules.insert(item.path.clone(), ast::Module::empty());
                        work.push(item.path.clone());
                    }
                }
            }
        }

        if implicit_prelude && !modules.contains_key(&prelude_path) {
            modules.insert(prelude_path.clone(), ast::Module::empty());
            work.push(prelude_path.clone());
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

    pub fn print(&self) {
        for (i, (module_path, module)) in self.modules.iter().enumerate() {
            if i != 0 {
                println!();
            }
            println!("mod {} {{\n", module_path);
            module.print();
            println!("\n}} # {}", module_path);
        }
    }
}

fn no_implicit_prelude(import: &ast::L<ast::ImportDecl>) -> bool {
    let attr = match &import.node.attr {
        Some(attr) => &attr.expr.node,
        None => return false,
    };
    if let ast::Expr::ConSel(ast::Con {
        ty,
        con,
        user_ty_args,
        ..
    }) = attr
        && ty == &ast::Name::new_static("NoImplicitPrelude")
        && con.is_none()
        && user_ty_args.is_empty()
    {
        return true;
    }
    panic!(
        "{}: Weird `import` attribute: {}",
        loc_display(&import.loc),
        attr
    );
}
