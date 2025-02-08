type Result<T> = std::result::Result<T, ()>;
pub trait Writer {
    /// Write the given DER-encoded bytes as output.
    fn write(&mut self, slice: &[u8]) -> Result<()>;

    /// Write a single byte.
    fn write_byte(&mut self, byte: u8) -> Result<()> {
        self.write(&[byte])
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Length(u32);

impl Length {

    fn initial_octet(self) -> Option<u8> {
        unimplemented!()
    }

    fn encode(&self, writer: &mut impl Writer) -> Result<()> {
        match self.0.to_be_bytes() {
            [0, 0, bytes @ ..] => writer.write(&bytes),
            bytes => writer.write(&bytes),
        }
    }
}

fn main(){

}
