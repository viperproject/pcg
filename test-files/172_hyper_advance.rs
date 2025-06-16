use std::mem::MaybeUninit;

pub struct ReadBuf<'a> {
    raw: &'a mut [MaybeUninit<u8>],
    filled: usize,
    init: usize,
}

pub struct ReadBufCursor<'a> {
    buf: &'a mut ReadBuf<'a>,
}

impl ReadBufCursor<'_> {
    pub unsafe fn advance(&mut self, n: usize) {
        self.buf.filled = self.buf.filled.checked_add(n).expect("overflow");
        self.buf.init = self.buf.filled.max(self.buf.init);
    }
}

fn main() {}
