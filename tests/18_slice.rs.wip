struct Bucket<K, V> {
    // hash: HashValue,
    key: K,
    value: V,
}
pub struct Slice<K, V> {
    pub(crate) entries: [Bucket<K, V>],
}

impl<K, V> Slice<K, V> {

    pub fn from_slice(entries: &[Bucket<K, V>]) -> &Self {
        unimplemented!()
    }

    pub fn split_at(&self, index: usize) -> (&Self, &Self) {
        let (first, second) = self.entries.split_at(index);
        (Self::from_slice(first), Self::from_slice(second))
    }
}

fn main(){}
