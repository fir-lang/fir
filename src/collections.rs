pub use std::collections::hash_map::Entry;

pub type Map<K, V> = fnv::FnvHashMap<K, V>;

pub type Set<K> = fnv::FnvHashSet<K>;
