use std::{mem, future::Future};

unsafe fn remove_future_lifetime<'a, T>(
    ptr: *mut (dyn Future<Output = T> + 'a),
) -> *mut (dyn Future<Output = T> + 'static) {
    unsafe { mem::transmute(ptr) }
}

fn main(){}
