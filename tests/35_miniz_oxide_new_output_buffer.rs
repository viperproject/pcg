pub struct CallbackFunc<'a> {
    pub put_buf_func: &'a mut dyn FnMut(&[u8]) -> bool,
}

pub struct CallbackBuf<'a> {
    pub out_buf: &'a mut [u8],
}

enum CallbackOut<'a> {
    Func(CallbackFunc<'a>),
    Buf(CallbackBuf<'a>),
}

struct OutputBufferOxide<'a> {
    pub inner: &'a mut [u8],
    pub inner_pos: usize,
    pub local: bool,

    pub bit_buffer: u32,
    pub bits_in: u32,
}

/// Size of the buffer of lz77 encoded data.
pub const LZ_CODE_BUF_SIZE: usize = 64 * 1024;
/// Size of the output buffer.
pub const OUT_BUF_SIZE: usize = (LZ_CODE_BUF_SIZE * 13) / 10;

impl CallbackOut<'_> {
    fn new_output_buffer<'b>(
        &'b mut self,
        local_buf: &'b mut [u8],
        out_buf_ofs: usize,
    ) -> OutputBufferOxide<'b> {
        let is_local;
        let buf_len = OUT_BUF_SIZE - 16;
        let chosen_buffer = match *self {
            CallbackOut::Buf(ref mut cb) if cb.out_buf.len() - out_buf_ofs >= OUT_BUF_SIZE => {
                is_local = false;
                &mut cb.out_buf[out_buf_ofs..out_buf_ofs + buf_len]
            }
            _ => {
                is_local = true;
                &mut local_buf[..buf_len]
            }
        };

        OutputBufferOxide {
            inner: chosen_buffer,
            inner_pos: 0,
            local: is_local,
            bit_buffer: 0,
            bits_in: 0,
        }
    }
}

fn main(){

}
