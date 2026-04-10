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
        <Self as std::fmt::Display>::fmt(self, f)
    }
}

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.module.fmt(f)?;
        f.write_str("/")?;
        self.name.fmt(f)?;
        Ok(())
    }
}

impl Id {
    pub fn new(module: &ModulePath, name: &Name) -> Id {
        Id {
            module: module.clone(),
            name: name.clone(),
        }
    }
}
