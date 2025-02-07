use std::cmp::Ordering;

fn sift_down<T>(heap: &mut [T], mut origin: usize) {
    unimplemented!()
}

pub(crate) fn k_smallest_general<I>(iter: I, k: usize) -> Vec<I::Item>
where
    I: Iterator,
{
    let mut iter = iter.fuse();
    let mut storage: Vec<I::Item> = iter.by_ref().collect();

    let mut heap = &mut storage[..];
    while true {
        let last_idx = heap.len() - 1;
        heap = &mut heap[..last_idx];
        sift_down(heap, 0);
    }

    storage
}

fn main() {}
