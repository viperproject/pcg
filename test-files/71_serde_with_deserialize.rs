struct KeyValueSeqDeserialize<'de, V> {
    delegate: V,
    first: Option<DeContent<'de>>,
}

struct VisitorWrapper<'de, V> {
    delegate: V,
    is_human_readable: bool,
    first: Option<DeContent<'de>>,
}

pub(crate) enum DeContent<'de> {
    Bool(bool),

    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),

    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),

    F32(f32),
    F64(f64),

    Char(char),
    String(String),
    Str(&'de str),
    ByteBuf(Vec<u8>),
    Bytes(&'de [u8]),

    None,
    Some(Box<DeContent<'de>>),

    Unit,
    Newtype(Box<DeContent<'de>>),
    Seq(Vec<DeContent<'de>>),
    Map(Vec<(DeContent<'de>, DeContent<'de>)>),
}

impl<'de, V> DeserializeSeed<'de> for KeyValueSeqDeserialize<'de, V>
where
    V: Visitor<'de>,
{
    type Value = V::Value;

    fn deserialize<D>(mut self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        let is_human_readable = deserializer.is_human_readable();
        deserializer.deserialize_seq(VisitorWrapper {
            delegate: self.delegate,
            is_human_readable,
            // PCG: bb1[12] post_main: self.first↓'?13 before bb1[11]:PostMain -> _10 before bb1[12]:PostOperands↓'?17 before bb1[12]:PostMain
            first: self.first.take(),
        })
    }
}

pub trait Deserializer<'de>: Sized {
    type Error;
    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>;

    fn is_human_readable(&self) -> bool {
        true
    }
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

fn main(){}


pub trait Visitor<'de>: Sized {
    /// The value produced by this visitor.
    type Value;
}

impl<'de, V> Visitor<'de> for VisitorWrapper<'de, V>
where
    V: Visitor<'de>,
{
    type Value = V::Value;
}
