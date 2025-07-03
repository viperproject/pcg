use std::collections::BTreeSet;

use crate::r#loop::LoopId;

#[derive(Clone, Debug)]
pub(super) struct LoopSet {
    data: BTreeSet<LoopId>,
}

impl LoopSet {
    pub(super) fn new() -> Self {
        Self {
            data: BTreeSet::new(),
        }
    }
    pub(super) fn add(&mut self, loop_idx: LoopId) {
        self.data.insert(loop_idx);
    }

    /// Adds all loops in `other` to this set.
    pub(super) fn merge(&mut self, other: &Self) {
        self.data.extend(other.data.iter().copied());
    }

    /// Removes the loop from the set.
    pub(super) fn remove(&mut self, loop_idx: LoopId) {
        self.data.remove(&loop_idx);
    }
    pub(super) fn contains(&self, loop_idx: LoopId) -> bool {
        self.data.contains(&loop_idx)
    }
    pub(super) fn iter(&self) -> impl DoubleEndedIterator<Item = LoopId> + '_ {
        self.data.iter().copied()
    }
}

// TODO: Once everything works, use an optimized implementation like this one:
//
// #[derive(Clone, Debug)]
// pub(super) struct LoopSet {
//     // Tracks up to 64 loops inline
//     data: smallvec::SmallVec<[u8; 8]>,
// }
// impl LoopSet {
//     const OFFSET: usize = 8 * std::mem::size_of::<u8>();

//     pub(super) fn new() -> Self {
//         Self {
//             data: smallvec::SmallVec::from_const([0; 8]),
//         }
//     }
//     pub(super) fn add(&mut self, loop_idx: LoopId) {
//         let loop_idx = loop_idx.index();
//         let idx = loop_idx / Self::OFFSET;
//         if idx >= self.data.len() {
//             self.data.resize(idx + 1, 0);
//         }
//         self.data[idx] |= 1 << (loop_idx % Self::OFFSET);
//     }
//     pub(super) fn merge(&mut self, other: &Self) {
//         if other.data.len() > self.data.len() {
//             self.data.resize(other.data.len(), 0);
//         }
//         for (idx, val) in other.data.iter().enumerate() {
//             self.data[idx] |= val;
//         }
//     }
//     pub(super) fn clear(&mut self, loop_idx: LoopId) {
//         let loop_idx = loop_idx.index();
//         let idx = loop_idx / Self::OFFSET;
//         assert!(idx < self.data.len());
//         self.data[idx] &= !(1 << (loop_idx % Self::OFFSET));
//     }
//     pub(super) fn contains(&self, loop_idx: LoopId) -> bool {
//         let loop_idx = loop_idx.index();
//         let idx = loop_idx / Self::OFFSET;
//         if idx >= self.data.len() {
//             return false;
//         }
//         self.data[idx] & (1 << (loop_idx % Self::OFFSET)) != 0
//     }
//     pub(super) fn iter(&self) -> impl DoubleEndedIterator<Item = LoopId> + '_ {
//         self.data.iter().enumerate().flat_map(|(idx, &val)| {
//             let to = if val == 0 { 0 } else { Self::OFFSET };
//             (0..to)
//                 .filter(move |&i| val & (1 << i) != 0)
//                 .map(move |i| LoopId::new(idx * Self::OFFSET + i))
//         })
//     }
// }
