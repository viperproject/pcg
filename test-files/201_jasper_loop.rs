
use std::convert::TryInto;

fn haha<'a, 'b>(baz: &'a mut &'b [u8]) -> &'a [u8] {
    let bar = &**baz;
    *baz = &[];
    bar
}

fn src_dst(src_0: &[u8], dst_0: &mut [u16]) {
    const SIZE: usize = core::mem::size_of::<u32>();
    let src_1: &[u8] = src_0;
    let dst_1: &mut [u16] = dst_0;
    assert_eq!(src_1.len(), dst_1.len() * SIZE);
    for (src_2, dst_2) in src_1.chunks_exact(SIZE).zip(dst_1.iter_mut()) {
        *dst_2 = <u16>::from_be_bytes(src_2.try_into().unwrap());
    }
}

fn main(){}
