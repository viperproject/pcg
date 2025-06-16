#[repr(i32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TDEFLStatus {
    /// Usage error.
    ///
    /// This indicates that either the [`CompressorOxide`] experienced a previous error, or the
    /// stream has already been [`TDEFLFlush::Finish`]'d.
    BadParam = -2,

    /// Error putting data into output buffer.
    ///
    /// This usually indicates a too-small buffer.
    PutBufFailed = -1,

    /// Compression succeeded normally.
    Okay = 0,

    /// Compression succeeded and the deflate stream was ended.
    ///
    /// This is the result of calling compression with [`TDEFLFlush::Finish`].
    Done = 1,
}

struct SavedOutputBufferOxide {
    pub pos: usize,
    pub bit_buffer: u32,
    pub bits_in: u32,
    pub local: bool,
}

pub(crate) struct ParamsOxide {
    pub flags: u32,
    pub greedy_parsing: bool,
    pub block_index: u32,
    pub prev_return_status: TDEFLStatus,
    pub flush_remaining: u32,
    pub local_buf: Box<LocalBuf>,
}

pub const LZ_CODE_BUF_SIZE: usize = 64 * 1024;
pub const OUT_BUF_SIZE: usize = (LZ_CODE_BUF_SIZE * 13) / 10;

pub struct LocalBuf {
    pub b: [u8; OUT_BUF_SIZE],
}

pub struct CallbackFunc<'a> {
    pub put_buf_func: &'a mut dyn FnMut(&[u8]) -> bool,
}

impl CallbackFunc<'_> {
    fn flush_output(
        &mut self,
        saved_output: SavedOutputBufferOxide,
        params: &mut ParamsOxide,
    ) -> i32 {
        // TODO: As this could be unsafe since
        // we can't verify the function pointer
        // this whole function should maybe be unsafe as well.
        let call_success = (self.put_buf_func)(&params.local_buf.b[0..saved_output.pos]);

        if !call_success {
            params.prev_return_status = TDEFLStatus::PutBufFailed;
            return params.prev_return_status as i32;
        }

        params.flush_remaining as i32
    }
}

fn main() {
}
