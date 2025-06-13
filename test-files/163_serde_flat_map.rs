use std::slice;
pub use std::error::Error as StdError;
use std::marker::PhantomData;
trait ErrorTrait: Sized + StdError {}

pub trait MapAccess<'de> {
    /// The error type that can be returned if some error occurs during
    /// deserialization.
    type Error: ErrorTrait;

    fn next_key_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: DeserializeSeed<'de>;
}

impl<'a, 'de, E> ContentRefDeserializer<'a, 'de, E> {
    /// private API, don't use
    pub fn new(content: &'a Content<'de>) -> Self {
        ContentRefDeserializer {
            content,
            err: PhantomData,
        }
    }
}

impl<'de, E: ErrorTrait> Deserializer<'de> for ContentRefDeserializer<'de, 'de, E> {
    type Error = E;
}


pub enum Content<'de> {
    Bool(bool),

    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),

    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),

    F32(f32),
    F64(f64),

    Char(char),
    String(String),
    Str(&'de str),
    ByteBuf(Vec<u8>),
    Bytes(&'de [u8]),

    None,
    Some(Box<Content<'de>>),
}

pub struct ContentRefDeserializer<'a, 'de: 'a, E> {
    content: &'a Content<'de>,
    err: PhantomData<E>,
}

struct FlatMapAccess<'a, 'de: 'a, E> {
    iter: slice::Iter<'a, Option<(Content<'de>, Content<'de>)>>,
    pending_content: Option<&'a Content<'de>>,
    _marker: PhantomData<E>,
}

pub trait Deserializer<'de>: Sized {
    /// The error type that can be returned if some error occurs during
    /// deserialization.
    type Error: ErrorTrait;
}

pub trait DeserializeSeed<'de>: Sized {
    /// The type produced by using this seed.
    type Value;

    /// Equivalent to the more common `Deserialize::deserialize` method, except
    /// with some initial piece of data (the seed) passed in.
    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>;
}

impl<'a: 'de, 'de, E> MapAccess<'de> for FlatMapAccess<'a, 'de, E>
where
    E: ErrorTrait,
{
    type Error = E;

    fn next_key_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        for item in &mut self.iter {
            // Items in the vector are nulled out when used by a struct.
            if let Some((ref key, ref content)) = *item {
                // Do not take(), instead borrow this entry. The internally tagged
                // enum does its own buffering so we can't tell whether this entry
                // is going to be consumed. Borrowing here leaves the entry
                // available for later flattened fields.
                self.pending_content = Some(content);
                return seed.deserialize(ContentRefDeserializer::new(key)).map(Some);
            }
        }
        Ok(None)
    }
}

fn main() {}
