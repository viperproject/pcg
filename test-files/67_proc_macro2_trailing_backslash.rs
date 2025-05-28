use std::slice;
use std::iter::Copied;

pub struct Bytes<'a>(Copied<slice::Iter<'a, u8>>);

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
}

struct Reject;

#[derive(Copy, Clone, Eq, PartialEq)]
pub(crate) struct Cursor<'a> {
    pub(crate) rest: &'a str
}

impl<'a> Cursor<'a> {
    fn bytes(&self) -> Bytes<'a> {
        unimplemented!()
    }

    pub(crate) fn advance(&self, bytes: usize) -> Cursor<'a> {
        unimplemented!()
    }
}


fn trailing_backslash(input: &mut Cursor, mut last: u8) -> Result<(), Reject> {
    let mut whitespace = input.bytes().enumerate();
    loop {
        if last == b'\r' && whitespace.next().map_or(true, |(_, b)| b != b'\n') {
            return Err(Reject);
        }
        match whitespace.next() {
            Some((_, b @ (b' ' | b'\t' | b'\n' | b'\r'))) => {
                last = b;
            }
            Some((offset, _)) => {
                *input = input.advance(offset);
                return Ok(());
            }
            None => return Err(Reject),
        }
    }
}

fn main(){ }
