pub(crate) struct BitsBuffer {
    bit_buffer: u32,
    bits_in_buffer: i32,
}

pub(crate) struct InputBuffer<'a> {
    pub bits: BitsBuffer,
    pub buffer: &'a [u8],
    pub read_bytes: usize,
}

impl<'a> InputBuffer<'a> {
    fn advance(&mut self, buf: usize) {
        self.buffer = &self.buffer[buf..];
        self.read_bytes += buf;
    }
}

fn main() {
}
