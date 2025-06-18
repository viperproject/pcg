
use std::fmt;

type Entries<K, V> = Vec<Bucket<K, V>>;

#[derive(Clone, Copy, PartialEq)]
struct HashValue(usize);

#[derive(Clone, Copy)]
struct Bucket<K, V> {
    hash: HashValue,
    key: K,
    value: V,
}

type Indices = ();

struct RefMut<'a, K, V> {
    indices: &'a mut Indices,
    entries: &'a mut Entries<K, V>,
}

pub struct VacantEntry<'a, K, V> {
    map: RefMut<'a, K, V>,
    hash: HashValue,
    key: K,
}

pub struct OccupiedEntry<'a, K, V> {
    entries: &'a mut Entries<K, V>,
    index: ()
}

impl <K: fmt::Debug, V: fmt::Debug> fmt::Debug for VacantEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}

impl <K: fmt::Debug, V: fmt::Debug> fmt::Debug for OccupiedEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}

pub enum Entry<'a, K, V> {
    /// Existing slot with equivalent key.
    Occupied(OccupiedEntry<'a, K, V>),
    /// Vacant slot (no equivalent key in the map).
    Vacant(VacantEntry<'a, K, V>),
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Entry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tuple = f.debug_tuple("Entry");
        match self {
            Entry::Vacant(v) => tuple.field(v),
            Entry::Occupied(o) => tuple.field(o),
        };
        tuple.finish()
    }
}

fn main(){}
