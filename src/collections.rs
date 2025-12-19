#![allow(unused)]

pub use std::collections::hash_map::Entry;

pub use crate::scope_map::{ScopeMap, ScopeSet};

pub use ordermap::{OrderMap, OrderSet};

pub type HashMap<K, V> = fnv::FnvHashMap<K, V>;

pub type HashSet<K> = fnv::FnvHashSet<K>;

pub type OrdMap<K, V> = std::collections::BTreeMap<K, V>;

pub type OrdSet<K> = std::collections::BTreeSet<K>;
