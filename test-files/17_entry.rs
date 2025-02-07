type Entries<K, V> = Vec<Bucket<K, V>>;

struct Bucket<K, V> {
    // hash: HashValue,
    key: K,
    value: V,
}
pub struct OccupiedEntry<'a, K, V> {
    entries: &'a mut Entries<K, V>,
    // index: hash_table::OccupiedEntry<'a, usize>,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub fn index(&self) -> usize {
        unimplemented!()
    }
    pub fn key(&self) -> &K {
        &self.entries[self.index()].key
    }
}

fn main() {}
