pub struct TokenStream {
    inner: (),
    _marker: (),
}

enum Entry {
    End(isize, isize),
}

pub struct TokenBuffer {
    // NOTE: Do not implement clone on this - while the current design could be
    // cloned, other designs which could be desirable may not be cloneable.
    entries: Box<[Entry]>,
}

impl TokenBuffer {
    fn recursive_new(entries: &mut Vec<Entry>, stream: TokenStream) {
    }
    pub fn new2(stream: TokenStream) -> Self {
        let mut entries = Vec::new();
        Self::recursive_new(&mut entries, stream);
        entries.push(Entry::End(-(entries.len() as isize), 0));
        Self {
            entries: entries.into_boxed_slice(),
        }
    }
}

fn main(){}
