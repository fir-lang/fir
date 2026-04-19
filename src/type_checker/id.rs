use crate::collections::*;
use crate::module::ModulePath;
use crate::name::Name;

/// Reference to a definition in a module.
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id {
    /// Module of the type definition.
    module: ModulePath,

    /// Name of the type definition in its module.
    name: Name,
}

impl std::fmt::Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.name, f)
    }
}

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}

impl Id {
    pub fn new(module: &ModulePath, name: &Name) -> Id {
        Id {
            module: module.clone(),
            name: name.clone(),
        }
    }

    pub fn name(&self) -> &Name {
        &self.name
    }

    pub fn module(&self) -> &ModulePath {
        &self.module
    }
}

/// Well-known `Id`s for built-in types and traits.
#[allow(non_snake_case)]
pub(crate) mod builtins {
    use super::*;

    use smol_str::SmolStr;

    fn fir_id(module: &'static str, name: &'static str) -> Id {
        Id {
            module: ModulePath::new(vec![
                SmolStr::new_static("Fir"),
                SmolStr::new_static(module),
            ]),
            name: Name::new_static(name),
        }
    }

    fn prelude_id(name: &'static str) -> Id {
        fir_id("Prelude", name)
    }

    // Fir/Prelude
    pub fn BOOL() -> Id {
        prelude_id("Bool")
    }

    pub fn ORDERING() -> Id {
        prelude_id("Ordering")
    }

    pub fn TO_STR() -> Id {
        prelude_id("ToStr")
    }

    // Fir/Str
    pub fn STR() -> Id {
        fir_id("Str", "Str")
    }

    // Fir/StrBuf
    pub fn STR_BUF() -> Id {
        fir_id("StrBuf", "StrBuf")
    }

    // Fir/Char
    pub fn CHAR() -> Id {
        fir_id("Char", "Char")
    }

    // Fir/Num
    pub fn I8() -> Id {
        fir_id("Num", "I8")
    }

    pub fn U8() -> Id {
        fir_id("Num", "U8")
    }

    pub fn I32() -> Id {
        fir_id("Num", "I32")
    }

    pub fn U32() -> Id {
        fir_id("Num", "U32")
    }

    pub fn I64() -> Id {
        fir_id("Num", "I64")
    }

    pub fn U64() -> Id {
        fir_id("Num", "U64")
    }

    // Fir/Option
    pub fn OPTION() -> Id {
        fir_id("Option", "Option")
    }

    // Fir/Array
    pub fn ARRAY() -> Id {
        fir_id("Array", "Array")
    }

    // Fir/Iter
    pub fn ITERATOR() -> Id {
        fir_id("Iter", "Iterator")
    }

    pub fn EMPTY() -> Id {
        fir_id("Iter", "empty")
    }

    pub fn ONCE() -> Id {
        fir_id("Iter", "once")
    }

    // Fir/RowToList
    pub fn REC_ROW_TO_LIST() -> Id {
        fir_id("RowToList", "RecRowToList")
    }

    pub fn RECORD_FIELD() -> Id {
        fir_id("RowToList", "RecordField")
    }

    // Fir/List
    pub fn LIST() -> Id {
        fir_id("List", "List")
    }
}

/// Mangles `Id`s for code generation purposes.
#[derive(Debug)]
pub struct IdMangler {
    // Values here are `Name`s instead of `u32`s to avoid creating a new string on every lookup.
    // (`Name` is O(1) to clone)
    mangled: HashMap<Name, HashMap<ModulePath, Name>>,
}

impl IdMangler {
    pub fn new() -> IdMangler {
        IdMangler {
            mangled: Default::default(),
        }
    }

    pub fn mangle(&mut self, id: &Id) -> Name {
        let name_map = self.mangled.entry(id.name.clone()).or_default();
        let num_names = name_map.len() as u32;
        match name_map.entry(id.module.clone()) {
            Entry::Occupied(entry) => entry.get().clone(),
            Entry::Vacant(entry) => {
                if num_names == 0 {
                    entry.insert(id.name.clone()).clone()
                } else {
                    let str = Name::new(format!("{}${}", id.name, num_names));
                    entry.insert(str.clone());
                    str
                }
            }
        }
    }
}

#[test]
fn mangler_test() {
    let mut mangler = IdMangler::new();

    assert_eq!(
        mangler.mangle(&Id::new(
            &ModulePath::new(vec!["A".into(), "B".into()]),
            &Name::new("T")
        )),
        Name::new("T")
    );

    assert_eq!(
        mangler.mangle(&Id::new(
            &ModulePath::new(vec!["A".into(), "C".into()]),
            &Name::new("T")
        )),
        Name::new("T$1")
    );

    assert_eq!(
        mangler.mangle(&Id::new(
            &ModulePath::new(vec!["A".into(), "B".into()]),
            &Name::new("T")
        )),
        Name::new("T")
    );
}
