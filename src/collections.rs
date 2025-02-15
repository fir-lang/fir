#![allow(unused)]

pub use std::collections::hash_map::Entry;

pub use crate::scope_map::{ScopeMap, ScopeSet};

pub use ordermap::{OrderMap, OrderSet};

pub type Map<K, V> = fnv::FnvHashMap<K, V>;

pub type Set<K> = fnv::FnvHashSet<K>;

pub type TreeMap<K, V> = std::collections::BTreeMap<K, V>;

pub type TreeSet<K> = std::collections::BTreeSet<K>;
