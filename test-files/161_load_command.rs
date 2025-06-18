use std::marker::PhantomData;
pub trait Endian:  'static {
}
#[derive(Clone, Copy)]
pub struct Bytes<'data>(pub &'data [u8]);

impl<'data> Bytes<'data> {
    pub fn read<T>(&mut self) -> Result<&'data T> {
        unimplemented!()
    }
}
pub struct LoadCommandData<'data, E: Endian> {
    cmd: u32,
    // Includes the header.
    data: Bytes<'data>,
    marker: PhantomData<E>,
}

pub const LC_SEGMENT: u32 = 0x1;

pub struct U32Bytes<E: Endian>([u8; 4], PhantomData<E>);
pub type U32<E> = U32Bytes<E>;

pub struct SegmentCommand32<E: Endian> {
    /// LC_SEGMENT
    pub cmd: U32<E>,
    /// includes sizeof section structs
    pub cmdsize: U32<E>,
    /// segment name
    pub segname: [u8; 16],
    /// memory address of this segment
    pub vmaddr: U32<E>,
    /// memory size of this segment
    pub vmsize: U32<E>,
    /// file offset of this segment
    pub fileoff: U32<E>,
    /// amount to map from the file
    pub filesize: U32<E>,
    /// maximum VM protection
    pub maxprot: U32<E>,
    /// initial VM protection
    pub initprot: U32<E>,
    /// number of sections in segment
    pub nsects: U32<E>,
    /// flags
    pub flags: U32<E>,
}

pub type Result<T> = std::result::Result<T, ()>;

trait ReadError<T> {
    fn read_error(self, error: &'static str) -> Result<T>;
}

impl<T> ReadError<T> for std::result::Result<T, ()> {
    fn read_error(self, error: &'static str) -> Result<T> {
        unimplemented!()
    }
}

impl<'data, E: Endian> LoadCommandData<'data, E> {
    pub fn segment_32(self) -> Result<Option<(&'data SegmentCommand32<E>, &'data [u8])>> {
        if self.cmd == LC_SEGMENT {
            let mut data = self.data;
            let segment = data.read().read_error("Invalid Mach-O command size")?;
            Ok(Some((segment, data.0)))
        } else {
            Ok(None)
        }
    }
}

fn main(){}
