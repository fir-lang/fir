pub use crate::scope_map::{ScopeMap, ScopeSet};

pub type Map<K, V> = fnv::FnvHashMap<K, V>;

pub type Set<K> = fnv::FnvHashSet<K>;

pub type TreeMap<K, V> = std::collections::BTreeMap<K, V>;

#[allow(unused)]
pub type TreeSet<K> = std::collections::BTreeSet<K>;
