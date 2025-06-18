use std::borrow::Cow;

pub struct Captures<'h> {
    haystack: &'h [u8],
    // caps: captures::Captures,
    static_captures_len: Option<usize>,
}

impl<'h> Captures<'h> {
    pub fn expand(&self, replacement: &[u8], dst: &mut Vec<u8>) {
        unimplemented!()
    }
}

trait Replacer {
    fn replace_append(&mut self, caps: &Captures<'_>, dst: &mut Vec<u8>);
}

impl<'a> Replacer for Cow<'a, [u8]> {
    fn replace_append(&mut self, caps: &Captures<'_>, dst: &mut Vec<u8>) {
        caps.expand(self.as_ref(), dst);
    }
}

fn main() {}
