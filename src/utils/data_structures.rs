use crate::rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};
pub(crate) type HashSet<T> = FxHashSet<T>;
pub(crate) type HashMap<K, V> = FxHashMap<K, V>;
