use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use std::sync::Once;

impl<T> Drop for OnceLock<T> {
    fn drop(&mut self) {
        if self.once.is_completed() {
            // SAFETY: The inner value has been initialized
            unsafe { (*self.value.get()).assume_init_drop() };
        }
    }
}

pub(crate) struct OnceLock<T> {
    once: Once,
    value: UnsafeCell<MaybeUninit<T>>,
    // Unlike std::sync::OnceLock, we don't need PhantomData here because
    // we don't use #[may_dangle].
}


fn main(){}
