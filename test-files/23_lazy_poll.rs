use std::sync::atomic::{AtomicPtr, Ordering};

pub struct Lazy<T, F> {
    data: AtomicPtr<T>,
    create: F,
}

impl<T, F: Fn() -> T> Lazy<T, F> {
    fn poll(&self) -> Option<&T> {
        let ptr = self.data.load(Ordering::Acquire);
        if ptr.is_null() {
            return None;
        }
        // SAFETY: We just checked that the pointer is not null. Since it's
        // not null, it must have been fully initialized by 'get' at some
        // point.
        // PCG: PcgError { kind: Unsupported(DerefUnsafePtr), context: [] }
        Some(unsafe { &*ptr })
    }
}

fn main() {
}
