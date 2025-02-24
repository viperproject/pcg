use std::collections::hash_map::RandomState;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::hash::{BuildHasher, Hash, Hasher};
use std::iter::{FromIterator, FusedIterator};
use std::marker::PhantomData;
use std::{fmt, mem, ops, ptr, vec};

struct HeaderValue;
struct HeaderName;


pub struct HeaderMap<T = HeaderValue> {
    // Used to mask values to get an index
    mask: Size,
    indices: Box<[Pos]>,
    entries: Vec<Bucket<T>>,
    extra_values: Vec<ExtraValue<T>>,
    danger: Danger,
}

pub struct Iter<'a, T> {
    map: &'a HeaderMap<T>,
    entry: usize,
    cursor: Option<Cursor>,
}

pub struct IterMut<'a, T> {
    map: *mut HeaderMap<T>,
    entry: usize,
    cursor: Option<Cursor>,
    lt: PhantomData<&'a mut HeaderMap<T>>,
}

pub struct IntoIter<T> {
    // If None, pull from `entries`
    next: Option<usize>,
    entries: vec::IntoIter<Bucket<T>>,
    extra_values: Vec<ExtraValue<T>>,
}

pub struct Keys<'a, T> {
    inner: ::std::slice::Iter<'a, Bucket<T>>,
}

/// `HeaderMap` value iterator.
///
/// Each value contained in the `HeaderMap` will be yielded.
pub struct Values<'a, T> {
    inner: Iter<'a, T>,
}

/// `HeaderMap` mutable value iterator
pub struct ValuesMut<'a, T> {
    inner: IterMut<'a, T>,
}

/// A drain iterator for `HeaderMap`.
pub struct Drain<'a, T> {
    idx: usize,
    len: usize,
    entries: *mut [Bucket<T>],
    // If None, pull from `entries`
    next: Option<usize>,
    extra_values: *mut Vec<ExtraValue<T>>,
    lt: PhantomData<&'a mut HeaderMap<T>>,
}

/// A view to all values stored in a single entry.
///
/// This struct is returned by `HeaderMap::get_all`.
pub struct GetAll<'a, T> {
    map: &'a HeaderMap<T>,
    index: Option<usize>,
}

/// A view into a single location in a `HeaderMap`, which may be vacant or occupied.
pub enum Entry<'a, T: 'a> {
    /// An occupied entry
    Occupied(OccupiedEntry<'a, T>),

    /// A vacant entry
    Vacant(VacantEntry<'a, T>),
}

/// A view into a single empty location in a `HeaderMap`.
///
/// This struct is returned as part of the `Entry` enum.
pub struct VacantEntry<'a, T> {
    map: &'a mut HeaderMap<T>,
    key: HeaderName,
    hash: HashValue,
    probe: usize,
    danger: bool,
}

/// A view into a single occupied location in a `HeaderMap`.
///
/// This struct is returned as part of the `Entry` enum.
pub struct OccupiedEntry<'a, T> {
    map: &'a mut HeaderMap<T>,
    probe: usize,
    index: usize,
}

/// An iterator of all values associated with a single header name.
pub struct ValueIter<'a, T> {
    map: &'a HeaderMap<T>,
    index: usize,
    front: Option<Cursor>,
    back: Option<Cursor>,
}

/// A mutable iterator of all values associated with a single header name.
pub struct ValueIterMut<'a, T> {
    map: *mut HeaderMap<T>,
    index: usize,
    front: Option<Cursor>,
    back: Option<Cursor>,
    lt: PhantomData<&'a mut HeaderMap<T>>,
}

/// An drain iterator of all values associated with a single header name.
pub struct ValueDrain<'a, T> {
    first: Option<T>,
    next: Option<::std::vec::IntoIter<T>>,
    lt: PhantomData<&'a mut HeaderMap<T>>,
}

/// Error returned when max capacity of `HeaderMap` is exceeded
pub struct MaxSizeReached {
    _priv: (),
}

/// Tracks the value iterator state
#[derive(Eq, PartialEq)]
enum Cursor {
    Head,
    Values(usize),
}

type Size = u16;

/// This limit falls out from above.
const MAX_SIZE: usize = 1 << 15;

/// An entry in the hash table. This represents the full hash code for an entry
/// as well as the position of the entry in the `entries` vector.
#[derive(Copy, Clone)]
struct Pos {
    // Index in the `entries` vec
    index: Size,
    // Full hash value for the entry.
    hash: HashValue,
}

impl Pos {
    fn none() -> Self {
        Self {
            index: Size::MAX,
            hash: HashValue(0),
        }
    }

    fn resolve(&self) -> Option<(usize, HashValue)> {
        if self.index == Size::MAX {
            None
        } else {
            Some((self.index as usize, self.hash))
        }
    }

    fn new(index: usize, hash: HashValue) -> Self {
        Self {
            index: index as Size,
            hash,
        }
    }
}

fn desired_pos(mask: Size, hash: HashValue) -> usize {
    hash.0 as usize & mask as usize
}

#[derive(Copy, Clone, Eq, PartialEq)]
struct HashValue(u16);

struct Bucket<T> {
    hash: HashValue,
    key: HeaderName,
    value: T,
    links: Option<Links>,
}

/// The head and tail of the value linked list.
#[derive(Copy, Clone)]
struct Links {
    next: usize,
    tail: usize,
}

/// Access to the `links` value in a slice of buckets.
///
/// It's important that no other field is accessed, since it may have been
/// freed in a `Drain` iterator.
struct RawLinks<T>(*mut [Bucket<T>]);

/// Node in doubly-linked list of header value entries
struct ExtraValue<T> {
    value: T,
    prev: Link,
    next: Link,
}

/// A header value node is either linked to another node in the `extra_values`
/// list or it points to an entry in `entries`. The entry in `entries` is the
/// start of the list and holds the associated header name.
enum Link {
    Entry(usize),
    Extra(usize),
}

/// Tracks the header map danger level! This relates to the adaptive hashing
/// algorithm. A HeaderMap starts in the "green" state, when a large number of
/// collisions are detected, it transitions to the yellow state. At this point,
/// the header map will either grow and switch back to the green state OR it
/// will transition to the red state.
///
/// When in the red state, a safe hashing algorithm is used and all values in
/// the header map have to be rehashed.
#[derive(Clone)]
enum Danger {
    Green,
    Yellow,
    Red(RandomState),
}

// Constants related to detecting DOS attacks.
//
// Displacement is the number of entries that get shifted when inserting a new
// value. Forward shift is how far the entry gets stored from the ideal
// position.
//
// The current constant values were picked from another implementation. It could
// be that there are different values better suited to the header map case.
const DISPLACEMENT_THRESHOLD: usize = 128;
const FORWARD_SHIFT_THRESHOLD: usize = 512;

// The default strategy for handling the yellow danger state is to increase the
// header map capacity in order to (hopefully) reduce the number of collisions.
// If growing the hash map would cause the load factor to drop bellow this
// threshold, then instead of growing, the headermap is switched to the red
// danger state and safe hashing is used instead.
const LOAD_FACTOR_THRESHOLD: f32 = 0.2;

impl<T> HeaderMap<T> {
    fn remove_found(&mut self, probe: usize, found: usize) -> Bucket<T> {
        let entry = self.entries.swap_remove(found);

        // correct index that points to the entry that had to swap places
        if let Some(entry) = self.entries.get(found) {
            let mut probe = desired_pos(self.mask, entry.hash);

            loop {
                if let Some((i, _)) = self.indices[probe].resolve() {
                    if i >= self.entries.len() {
                        // found it
                        self.indices[probe] = Pos::new(found, entry.hash);
                        // break;
                    }
                }
            }

        }

        entry
    }
}

fn main(){}
