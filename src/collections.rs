pub use crate::scope_map::{ScopeMap, ScopeSet};

pub type Map<K, V> = fnv::FnvHashMap<K, V>;

pub type Set<K> = fnv::FnvHashSet<K>;
