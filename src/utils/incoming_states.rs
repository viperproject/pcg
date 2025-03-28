use crate::rustc_interface::middle::mir;
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IncomingStates(BTreeSet<mir::BasicBlock>);

impl Default for IncomingStates {
    fn default() -> Self {
        Self::new()
    }
}

impl IncomingStates {
    pub(crate) fn new() -> Self {
        Self(BTreeSet::new())
    }

    pub(crate) fn insert(&mut self, block: mir::BasicBlock) {
        self.0.insert(block);
    }

    pub(crate) fn singleton(block: mir::BasicBlock) -> Self {
        let mut s = Self::new();
        s.insert(block);
        s
    }

    pub(crate) fn contains(&self, block: mir::BasicBlock) -> bool {
        self.0.contains(&block)
    }

}
