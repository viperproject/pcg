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
