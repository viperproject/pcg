use std::mem;
use std::collections::hash_map;
use std::collections::HashMap;
use std::hash::BuildHasher;
use std::borrow::Borrow;
use std::hash::Hash;

#[derive(Hash, PartialEq, Eq)]
#[repr(transparent)]
struct Qey<Q: ?Sized>(Q);

struct Node<K, V> {
    next: *mut Node<K, V>,
    prev: *mut Node<K, V>,
    key: K,
    value: V,
}

impl<K, Q: ?Sized> Borrow<Qey<Q>> for KeyRef<K>
where
    K: Borrow<Q>,
{
    fn borrow(&self) -> &Qey<Q> {
        Qey::from_ref(unsafe { (*self.k).borrow() })
    }
}

#[derive(Hash, PartialEq, Eq)]
struct KeyRef<K> {
    k: *const K,
}

impl<Q: ?Sized> Qey<Q> {
    fn from_ref(q: &Q) -> &Self {
        unsafe { mem::transmute(q) }
    }
}

pub struct LinkedHashMap<K, V, S = hash_map::RandomState> {
    map: HashMap<KeyRef<K>, *mut Node<K, V>, S>,
    head: *mut Node<K, V>,
    free: *mut Node<K, V>,
}

impl<K: Hash + Eq, V, S: BuildHasher> LinkedHashMap<K, V, S> {
    pub fn get_refresh<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        let (value, node_ptr_opt) = match self.map.get(Qey::from_ref(k)) {
            None => (None, None),
            Some(node) => (Some(unsafe { &mut (**node).value }), Some(*node)),
        };
        if let Some(node_ptr) = node_ptr_opt {
            self.detach(node_ptr);
            self.attach(node_ptr);
        }
        value
    }

    fn detach(&mut self, node: *mut Node<K, V>) {
        unsafe {
            (*(*node).prev).next = (*node).next;
            (*(*node).next).prev = (*node).prev;
        }
    }

    #[inline]
    fn attach(&mut self, node: *mut Node<K, V>) {
        unsafe {
            (*node).next = (*self.head).next;
            (*node).prev = self.head;
            (*self.head).next = node;
            (*(*node).next).prev = node;
        }
    }
}

fn main(){

}
