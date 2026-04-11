use smol_str::SmolStr;

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
}

/// Well-known `Id`s for built-in types and traits.
#[allow(non_snake_case, dead_code)]
pub mod builtins {
    use super::*;

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

    pub fn EQ() -> Id {
        prelude_id("Eq")
    }

    pub fn ORD() -> Id {
        prelude_id("Ord")
    }

    pub fn HASH() -> Id {
        prelude_id("Hash")
    }

    pub fn CLONE() -> Id {
        prelude_id("Clone")
    }

    pub fn ADD() -> Id {
        prelude_id("Add")
    }

    pub fn SUB() -> Id {
        prelude_id("Sub")
    }

    pub fn MUL() -> Id {
        prelude_id("Mul")
    }

    pub fn DIV() -> Id {
        prelude_id("Div")
    }

    pub fn NEG() -> Id {
        prelude_id("Neg")
    }

    pub fn REM() -> Id {
        prelude_id("Rem")
    }

    pub fn BIT_OR() -> Id {
        prelude_id("BitOr")
    }

    pub fn BIT_XOR() -> Id {
        prelude_id("BitXor")
    }

    pub fn BIT_AND() -> Id {
        prelude_id("BitAnd")
    }

    pub fn SHL() -> Id {
        prelude_id("Shl")
    }

    pub fn SHR() -> Id {
        prelude_id("Shr")
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

    // Fir/Result
    pub fn RESULT() -> Id {
        fir_id("Result", "Result")
    }

    // Fir/Array
    pub fn ARRAY() -> Id {
        fir_id("Array", "Array")
    }

    // Fir/Vec
    pub fn VEC() -> Id {
        fir_id("Vec", "Vec")
    }

    // Fir/Iter
    pub fn ITERATOR() -> Id {
        fir_id("Iter", "Iterator")
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
