use std::{mem, future::Future};

unsafe fn remove_future_lifetime<'a, T>(
    ptr: *mut (dyn Future<Output = T> + 'a),
) -> *mut (dyn Future<Output = T> + 'static) {
    // PCG: PcgError { kind: Unsupported(MoveUnsafePtrWithNestedLifetime), context: [] }
    unsafe { mem::transmute(ptr) }
}

unsafe fn remove_drop_lifetime<'a, T>(
    ptr: unsafe fn(*mut (dyn Future<Output = T> + 'a)),
) -> unsafe fn(*mut (dyn Future<Output = T> + 'static)) {
    unsafe { mem::transmute(ptr) }
}

fn main(){}
