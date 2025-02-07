/// A `&[u8]` slice with endianity metadata.
///
/// This implements the `Reader` trait, which is used for all reading of DWARF sections.
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EndianSlice<'input, Endian>
{
    slice: &'input [u8],
    endian: Endian,
}

pub enum Error {
    UnexpectedEof(ReaderOffsetId),
}


/// The result of a parse.
pub type Result<T> = std::result::Result<T, Error>;

pub struct ReaderOffsetId(pub u64);


impl<'input, Endian> EndianSlice<'input, Endian>
{
    fn read_slice(&mut self, len: usize) -> Result<&'input [u8]> {
        if self.slice.len() < len {
            Err(Error::UnexpectedEof(self.offset_id()))
        } else {
            let val = &self.slice[..len];
            self.slice = &self.slice[len..];
            Ok(val)
        }
    }

    fn offset_id(&self) -> ReaderOffsetId {
        unimplemented!()
    }
}

fn main(){

}
