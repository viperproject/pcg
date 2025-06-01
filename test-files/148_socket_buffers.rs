use std::marker::PhantomData;
use std::ffi::c_void;
use std::mem::MaybeUninit;
struct msghdr;


struct iovec {
    pub iov_base: *mut c_void,
}

struct MaybeUninitSlice<'a> {
    vec: iovec,
    _lifetime: PhantomData<&'a mut [MaybeUninit<u8>]>,
}

pub struct MsgHdrMut<'addr, 'bufs, 'control> {
    inner: msghdr,
    #[allow(clippy::type_complexity)]
    _lifetimes: PhantomData<(
        &'addr mut (),
        &'bufs mut (),
        &'control mut (),
    )>,
}
fn set_msghdr_iov(msg: &mut msghdr, ptr: *mut iovec, len: usize) {
}

impl<'addr, 'bufs, 'control> MsgHdrMut<'addr, 'bufs, 'control> {
    pub fn with_buffers(mut self, bufs: &'bufs mut [MaybeUninitSlice<'_>]) -> Self {
        set_msghdr_iov(&mut self.inner, bufs.as_mut_ptr().cast(), bufs.len());
        self
    }
}

fn main() {}
