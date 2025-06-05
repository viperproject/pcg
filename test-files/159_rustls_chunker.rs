pub enum OutboundChunks<'a> {
    /// A single byte slice. Contrary to `Multiple`, this uses a single pointer indirection
    Single(&'a [u8]),
    /// A collection of chunks (byte slices)
    /// and cursors to single out a fragmented range of bytes.
    /// OutboundChunks assumes that start <= end
    Multiple {
        chunks: &'a [&'a [u8]],
        start: usize,
        end: usize,
    },
}

impl<'a> OutboundChunks<'a> {
    fn is_empty(&self) -> bool {
        false
    }

    pub fn split_at(&self, mid: usize) -> (Self, Self) {
        unimplemented!()
    }
}


struct Chunker<'a> {
    payload: OutboundChunks<'a>,
    limit: usize,
}


impl<'a> Iterator for Chunker<'a> {
    type Item = OutboundChunks<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.payload.is_empty() {
            return None;
        }

        let (before, after) = self.payload.split_at(self.limit);
        self.payload = after;
        Some(before)
    }
}

fn main(){}
