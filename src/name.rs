use std::borrow::Borrow;
use std::ops::Deref;

use smol_str::SmolStr;

/// An identifier in Fir source code.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(SmolStr);

impl Name {
    pub fn new(s: impl Into<SmolStr>) -> Self {
        Name(s.into())
    }

    pub const fn new_static(s: &'static str) -> Self {
        Name(SmolStr::new_static(s))
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}

impl std::fmt::Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, f)
    }
}

impl Deref for Name {
    type Target = SmolStr;

    fn deref(&self) -> &SmolStr {
        &self.0
    }
}

impl Borrow<str> for Name {
    fn borrow(&self) -> &str {
        self.0.as_str()
    }
}

impl Borrow<SmolStr> for Name {
    fn borrow(&self) -> &SmolStr {
        &self.0
    }
}

impl From<SmolStr> for Name {
    fn from(s: SmolStr) -> Self {
        Name(s)
    }
}

impl From<&str> for Name {
    fn from(s: &str) -> Self {
        Name(SmolStr::new(s))
    }
}

impl From<&SmolStr> for Name {
    fn from(s: &SmolStr) -> Self {
        Name(s.clone())
    }
}

impl From<String> for Name {
    fn from(s: String) -> Self {
        Name(SmolStr::new(s))
    }
}

impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool {
        self.0.as_str() == other
    }
}

impl PartialEq<&str> for Name {
    fn eq(&self, other: &&str) -> bool {
        self.0.as_str() == *other
    }
}

impl PartialEq<SmolStr> for Name {
    fn eq(&self, other: &SmolStr) -> bool {
        &self.0 == other
    }
}

impl PartialEq<Name> for SmolStr {
    fn eq(&self, other: &Name) -> bool {
        self == &other.0
    }
}

impl PartialEq<Name> for str {
    fn eq(&self, other: &Name) -> bool {
        self == other.0.as_str()
    }
}
