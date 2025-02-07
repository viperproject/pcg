#![feature(allocator_api)]
use std::{alloc::{Allocator, Global}, marker::PhantomData, ptr::NonNull};

pub struct HashTable<T, A = Global>
where
    A: Allocator,
{
    pub(crate) raw: RawTable<T, A>,
}


pub struct RawTable<T, A: Allocator = Global> {
    table: RawTableInner,
    alloc: A,
    // Tell dropck that we own instances of T.
    marker: PhantomData<T>,
}

struct RawTableInner {
    // Mask to get an index from a hash value. The value is one less than the
    // number of buckets in the table.
    bucket_mask: usize,

    // [Padding], T_n, ..., T1, T0, C0, C1, ...
    //                              ^ points here
    ctrl: NonNull<u8>,

    // Number of elements that can be inserted before we need to grow the table
    growth_left: usize,

    // Number of elements in the table, only really used by len()
    items: usize,
}


impl<T, A: Allocator> HashTable<T, A> {
    pub fn len(&self) -> usize {
        unimplemented!()
    }
    pub fn shrink_to_fit(&mut self, hasher: impl Fn(&T) -> u64) {
        self.raw.shrink_to(self.len(), hasher);
    }
}

impl<T, A: Allocator> RawTable<T, A> {
    pub fn shrink_to(&mut self, min_size: usize, hasher: impl Fn(&T) -> u64) {
        unimplemented!()
    }
}

fn main(){

}

