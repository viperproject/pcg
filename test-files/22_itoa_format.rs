use std::mem::MaybeUninit;

pub trait Integer {
    type Buffer: Sized;
    const MAX_STR_LEN: usize;

    fn write(self, buf: &mut [MaybeUninit<u8>; 1024]) -> &str;
}

struct Buffer {
    bytes: [MaybeUninit<u8>; 1024],
}

impl Buffer {
    pub fn format<I: Integer>(&mut self, i: I) -> &str {
        // PCG: PcgError { kind: Unsupported(DerefUnsafePtr), context: [] }
        let string = i.write(unsafe {
            &mut *(&mut self.bytes as *mut [MaybeUninit<u8>; 1024]
                as *mut [MaybeUninit<u8>; 1024])
        });
        // if string.len() > I::MAX_STR_LEN {
        //     unsafe { hint::unreachable_unchecked() };
        // }
        string
    }
}

fn main(){}
