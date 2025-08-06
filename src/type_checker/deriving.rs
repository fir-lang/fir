/*
TODOs and notes:
----------------

Derive macros should declare what they're deriving so that we can type check without generating the
code.

To be able to type check top-level items in parallel, a macro invocation like `derive(Eq)` in an
item should just update the type environment with the traits its implementing. The actual
implementation should then be generated and type checked in parallel just like other hand-written
top-level items.
*/

use crate::ast::Id;
use crate::collections::Map;

use smol_str::SmolStr;

/// Caches derive macro programs so that we don't read, parse, type check, lower, etc. the same
/// deriving macro for every invocation in a program.
pub(crate) struct DeriveMacroRunner {
    fir_root: String,
    macros: Map<Id, InterpretedPgm>,
}

pub(crate) struct InterpretedPgm {
    pub(crate) pgm: crate::interpreter::Pgm,
    pub(crate) heap: crate::interpreter::heap::Heap,
}

impl DeriveMacroRunner {
    pub fn new(fir_root: String) -> Self {
        DeriveMacroRunner {
            fir_root,
            macros: Default::default(),
        }
    }

    pub fn get_macro_runner(&mut self, macro_: &Id) -> &mut InterpretedPgm {
        if self.macros.contains_key(macro_) {
            self.macros.get_mut(macro_).unwrap()
        } else {
            let pgm = self.load_macro(macro_);
            self.macros.insert(macro_.clone(), pgm);
            self.macros.get_mut(macro_).unwrap()
        }
    }

    fn load_macro(&mut self, macro_: &Id) -> InterpretedPgm {
        let path = format!("compiler/Derive{}.fir", macro_);

        let file_path = std::path::Path::new(&path); // "examples/Foo.fir"
        let file_name_wo_ext = file_path.file_stem().unwrap(); // "Foo"
        let root_path = file_path.parent().unwrap(); // "examples/"

        let module =
            crate::parse_file(file_path, &SmolStr::new(file_name_wo_ext.to_str().unwrap()));

        let mut import_paths: Map<String, String> = Default::default();
        import_paths.insert("Fir".to_string(), self.fir_root.clone());

        let mut module = crate::import_resolver::resolve_imports(
            &import_paths,
            root_path.to_str().unwrap(),
            module,
            true, // import prelude
        );

        crate::type_checker::check_module(&mut module, &self.fir_root);

        let mut mono_pgm = crate::monomorph::monomorphise(&module, "main");

        let lowered_pgm = crate::lowering::lower(&mut mono_pgm);

        let mut heap = crate::interpreter::heap::Heap::new();
        let pgm = crate::interpreter::Pgm::init(lowered_pgm, &mut heap);
        InterpretedPgm { heap, pgm }
    }
}
