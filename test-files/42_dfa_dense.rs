use std::convert::TryFrom;
use std::mem::size_of;

pub(crate) trait Endian {
    fn write_u32(n: u32, dst: &mut [u8]);
}

#[derive(Debug)]
pub struct SerializeError {
    kind: ErrorKind,
}

#[derive(Debug)]
enum ErrorKind {
    BufferTooSmall,
}

impl SerializeError {
    fn buffer_too_small(_msg: &str) -> Self {
        SerializeError { kind: ErrorKind::BufferTooSmall }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct StateID(u32);

impl StateID {
    fn as_u32(&self) -> u32 {
        self.0
    }
}

mod wire {
    use super::*;
    pub(crate) fn write_state_id<E: Endian>(sid: u32, dst: &mut [u8]) -> usize {
        E::write_u32(sid, dst);
        size_of::<u32>()
    }
}

#[derive(Debug)]
pub(crate) enum StartKind {
    Unanchored,
    Anchored,
}

impl StartKind {
    fn write_to<E: Endian>(&self, dst: &mut [u8]) -> Result<usize, SerializeError> {
        Ok(size_of::<u32>())
    }
}

pub(crate) struct StartByteMap;

impl StartByteMap {
    fn write_to(&self, _dst: &mut [u8]) -> Result<usize, SerializeError> {
        Ok(0)
    }
}

pub(crate) struct StartTable<T> {
    table: T,
    kind: StartKind,
    start_map: StartByteMap,
    stride: usize,
    pattern_len: Option<usize>,
    universal_start_unanchored: Option<StateID>,
    universal_start_anchored: Option<StateID>,
}

impl<T: AsRef<[u32]>> StartTable<T> {
    fn write_to_len(&self) -> usize {
        size_of::<u32>() * (4 + self.table.as_ref().len())
    }

    fn table(&self) -> &[u32] {
        self.table.as_ref()
    }

    /// Writes a serialized form of this start table to the buffer given. If
    /// the buffer is too small, then an error is returned. To determine how
    /// big the buffer must be, use `write_to_len`.
    fn write_to<E: Endian>(
        &self,
        mut dst: &mut [u8],
    ) -> Result<usize, SerializeError> {
        let nwrite = self.write_to_len();
        if dst.len() < nwrite {
            return Err(SerializeError::buffer_too_small(
                "starting table ids",
            ));
        }
        dst = &mut dst[..nwrite];

        // write start kind
        let nw = self.kind.write_to::<E>(dst)?;
        dst = &mut dst[nw..];
        // write start byte map
        let nw = self.start_map.write_to(dst)?;
        dst = &mut dst[nw..];
        // write stride
        // Unwrap is OK since the stride is always 4 (currently).
        E::write_u32(u32::try_from(self.stride).unwrap(), dst);
        dst = &mut dst[size_of::<u32>()..];
        // write pattern length
        // Unwrap is OK since number of patterns is guaranteed to fit in a u32.
        E::write_u32(
            u32::try_from(self.pattern_len.unwrap_or(0xFFFF_FFFF)).unwrap(),
            dst,
        );
        dst = &mut dst[size_of::<u32>()..];
        // write universal start unanchored state id, u32::MAX if absent
        E::write_u32(
            self.universal_start_unanchored
                .as_ref()
                .map_or(u32::MAX, |sid| sid.as_u32()),
            dst,
        );
        dst = &mut dst[size_of::<u32>()..];
        // write universal start anchored state id, u32::MAX if absent
        E::write_u32(
            self.universal_start_anchored
                .as_ref()
                .map_or(u32::MAX, |sid| sid.as_u32()),
            dst,
        );
        dst = &mut dst[size_of::<u32>()..];
        // write start IDs
        for &sid in self.table() {
            let n = wire::write_state_id::<E>(sid, &mut dst);
            dst = &mut dst[n..];
        }
        Ok(nwrite)
    }
}

fn main() {
}
