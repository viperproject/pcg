use std::{option, slice};
use std::mem::ManuallyDrop;
use std::iter::Iterator;
use std::ops::{Deref, DerefMut};

trait IterTrait<'a, T: 'a>: Iterator<Item = &'a T> + DoubleEndedIterator + ExactSizeIterator {
}

#[repr(transparent)]
pub(crate) struct NoDrop<T: ?Sized>(T);

impl<T: ?Sized> Deref for NoDrop<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: ?Sized> DerefMut for NoDrop<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub struct Iter<'a, T: 'a> {
    inner: NoDrop<dyn IterTrait<'a, T> + 'a>,
}


impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

fn main(){}
