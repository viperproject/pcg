use std::fmt::{Display, Formatter, self};
trait Engine {}
struct FormatterSink<'a, 'b: 'a> {
    f: &'a mut Formatter<'b>,
}

pub struct ChunkedEncoder<'e, E: Engine + ?Sized> {
    engine: &'e E,
}

trait Sink {
    type Error;
}

impl Sink for FormatterSink<'_, '_> {
    type Error = fmt::Error;
}

impl<'e, E: Engine + ?Sized> ChunkedEncoder<'e, E> {
    pub fn encode<S: Sink>(&self, bytes: &[u8], sink: &mut S) -> Result<(), S::Error> {
        unimplemented!()
    }
}

/// A convenience wrapper for base64'ing bytes into a format string without heap allocation.
pub struct Base64Display<'a, 'e, E: Engine> {
    bytes: &'a [u8],
    chunked_encoder: ChunkedEncoder<'e, E>,
}

impl<'a, 'e, E: Engine> Display for Base64Display<'a, 'e, E> {
    fn fmt(&self, formatter: &mut Formatter) -> Result<(), fmt::Error> {
        let mut sink = FormatterSink { f: formatter };
        unimplemented!()
    }
}

fn main(){}
