pub struct HashMap<K, V, S, A> {
    _marker: std::marker::PhantomData<(K, V, S, A)>,
}

impl<K, V, S, A> HashMap<K, V, S, A> {
    pub fn insert_unique_unchecked(&mut self, key: K, value: V) -> (&K, &mut V) {
        unimplemented!()
    }
}

pub struct HashSet<T, S, A> {
    pub(crate) map: HashMap<T, (), S, A>,
}

impl<T, S, A> HashSet<T, S, A> {
    pub fn insert_unique_unchecked(&mut self, value: T) -> &T {
        self.map.insert_unique_unchecked(value, ()).0
    }
}

fn main() {
}
