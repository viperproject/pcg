#![feature(allocator_api)]

pub type DefaultHashBuilder = ();

pub struct Bucket<T> {
    // Actually it is pointer to next element than element itself
    // this is needed to maintain pointer arithmetic invariants
    // keeping direct pointer to element introduces difficulty.
    // Using `NonNull` for variance and niche layout
    ptr: NonNull<T>,
}

use std::ptr::NonNull;
use std::collections::HashMap;
use std::fmt::Debug;
use std::alloc::{Allocator, Global};
use std::fmt;
pub struct OccupiedEntry<'a, K, V, S = DefaultHashBuilder, A: Allocator = Global> {
    hash: u64,
    elem: Bucket<(K, V)>,
    table: &'a mut (),
    phantom: std::marker::PhantomData<(S, A)>,
}

impl<'a, K, V, S, A: Allocator> OccupiedEntry<'a, K, V, S, A> {
    pub fn key(&self) -> &K {
        unimplemented!()
    }

    pub fn get(&self) -> &V {
        unimplemented!()
    }
}

pub struct OccupiedError<'a, K, V, S, A: Allocator = Global> {
    /// The entry in the map that was already occupied.
    pub entry: OccupiedEntry<'a, K, V, S, A>,
    /// The value which was not inserted, because the entry was already occupied.
    pub value: V,
}

impl<K: Debug, V: Debug, S, A: Allocator> fmt::Display for OccupiedError<'_, K, V, S, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "failed to insert {:?}, key {:?} already exists with value {:?}",
            self.value,
            self.entry.key(),
            self.entry.get(),
        )
    }
}

fn main(){

}
