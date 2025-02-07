use std::{fmt::{self, Display}, marker::PhantomData};

struct Expected;

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Unexpected<'a> {
    /// The input contained a boolean value that was not expected.
    Bool(bool),

    /// The input contained an unsigned integer `u8`, `u16`, `u32` or `u64` that
    /// was not expected.
    Unsigned(u64),

    /// The input contained a signed integer `i8`, `i16`, `i32` or `i64` that
    /// was not expected.
    Signed(i64),

    /// The input contained a floating point `f32` or `f64` that was not
    /// expected.
    Float(f64),

    /// The input contained a `char` that was not expected.
    Char(char),

    /// The input contained a `&str` or `String` that was not expected.
    Str(&'a str),

    /// The input contained a `&[u8]` or `Vec<u8>` that was not expected.
    Bytes(&'a [u8]),

    /// The input contained a unit `()` that was not expected.
    Unit,

    /// The input contained an `Option<T>` that was not expected.
    Option,

    /// The input contained a newtype struct that was not expected.
    NewtypeStruct,

    /// The input contained a sequence that was not expected.
    Seq,

    /// The input contained a map that was not expected.
    Map,

    /// The input contained an enum that was not expected.
    Enum,

    /// The input contained a unit variant that was not expected.
    UnitVariant,

    /// The input contained a newtype variant that was not expected.
    NewtypeVariant,

    /// The input contained a tuple variant that was not expected.
    TupleVariant,

    /// The input contained a struct variant that was not expected.
    StructVariant,

    /// A message stating what uncategorized thing the input contained that was
    /// not expected.
    ///
    /// The message should be a noun or noun phrase, not capitalized and without
    /// a period. An example message is "unoriginal superhero".
    Other(&'a str),
}

impl<'a> fmt::Display for Unexpected<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        use self::Unexpected::*;
        match *self {
            Bool(b) => write!(formatter, "boolean `{}`", b),
            Unsigned(i) => write!(formatter, "integer `{}`", i),
            Signed(i) => write!(formatter, "integer `{}`", i),
            Float(f) => write!(formatter, "floating point `{}`", f),
            Char(c) => write!(formatter, "character `{}`", c),
            Str(s) => write!(formatter, "string {:?}", s),
            Bytes(_) => write!(formatter, "byte array"),
            Unit => write!(formatter, "unit value"),
            Option => write!(formatter, "Option value"),
            NewtypeStruct => write!(formatter, "newtype struct"),
            Seq => write!(formatter, "sequence"),
            Map => write!(formatter, "map"),
            Enum => write!(formatter, "enum"),
            UnitVariant => write!(formatter, "unit variant"),
            NewtypeVariant => write!(formatter, "newtype variant"),
            TupleVariant => write!(formatter, "tuple variant"),
            StructVariant => write!(formatter, "struct variant"),
            Other(other) => formatter.write_str(other),
        }
    }
}

impl Display for Expected {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expected")
    }
}


trait Error: Sized {
    type Unexpected: Display;
    type Expected: Display;
    fn custom(err: impl Display) -> Self;
    fn invalid_value(unexp: Unexpected, exp: &Expected) -> Self {
        Error::custom(format_args!("invalid value: {}, expected {}", unexp, exp))
    }
}

fn main(){

}
