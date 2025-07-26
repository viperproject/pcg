//! Data structures for validity conditions.
use crate::{rustc_interface::middle::mir, utils::display::DisplayWithCompilerCtxt};
use bit_set::BitSet;
use itertools::Itertools;
use smallvec::SmallVec;

use crate::{rustc_interface::middle::mir::BasicBlock, utils::CompilerCtxt};

use crate::utils::json::ToJsonWithCompilerCtxt;

/// Represents transfer of control flow from the block `from` to the block `to`.
#[derive(Copy, PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct PathCondition {
    from: BasicBlock,
    to: BasicBlock,
}

impl PathCondition {
    pub fn new(from: BasicBlock, to: BasicBlock) -> Self {
        Self { from, to }
    }
    pub fn from(&self) -> BasicBlock {
        self.from
    }
    pub fn to(&self) -> BasicBlock {
        self.to
    }
}

/// Represents a path of execution in the code (a sequence of basic blocks)
#[derive(PartialEq, Eq, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct Path(Vec<BasicBlock>);

impl Path {
    pub fn new(block: BasicBlock) -> Self {
        Self(vec![block])
    }

    pub fn append(&mut self, block: BasicBlock) {
        self.0.push(block);
    }

    pub fn start(&self) -> BasicBlock {
        self.0[0]
    }

    pub fn end(&self) -> BasicBlock {
        self.0[self.0.len() - 1]
    }
}

/// Represents a subset of the successors of a block. When checking whether a
/// path satisfies the given validity conditions, it must be the case that for
/// every b -> b' in the path, if from = b, then b' must be in one of the
/// successors
#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct BranchChoices {
    from: BasicBlock,
    chosen: BitSet<u8>,
}

enum BranchChoicesJoinResult {
    CoversAllChoices,
    Changed,
    Unchanged,
}

impl BranchChoices {
    fn new(from: BasicBlock, num_successors: usize) -> Self {
        let mut chosen = BitSet::default();
        chosen.reserve_len_exact(num_successors);
        Self { from, chosen }
    }

    fn insert(&mut self, idx: usize) {
        assert!(self.chosen.len() <= idx);
        self.chosen.insert(idx);
    }

    pub fn from(&self) -> BasicBlock {
        self.from
    }

    pub fn successors(&self, body: &mir::Body<'_>) -> Vec<BasicBlock> {
        effective_successors(self.from, body)
    }

    fn includes_successor(&self, successor: BasicBlock, body: &mir::Body<'_>) -> bool {
        let successors = effective_successors(self.from, body);
        let pos = successors.iter().position(|s| s == &successor);
        if let Some(pos) = pos {
            self.chosen.contains(pos)
        } else {
            false
        }
    }

    fn join(&mut self, other: &Self, body: &mir::Body<'_>) -> BranchChoicesJoinResult {
        assert_eq!(self.from, other.from);
        let old_len = self.chosen.len();
        let successors = effective_successors(self.from, body);
        self.chosen.union_with(&other.chosen);
        if self.chosen.len() == old_len {
            BranchChoicesJoinResult::Unchanged
        } else if self.chosen.len() == successors.len() {
            BranchChoicesJoinResult::CoversAllChoices
        } else {
            BranchChoicesJoinResult::Changed
        }
    }
}

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for BranchChoices {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        let successors = effective_successors(self.from, ctxt.body());
        if self.chosen.len() == 1 {
            format!(
                "{:?} -> {:?}",
                self.from,
                successors[self.chosen.iter().next().unwrap()]
            )
        } else {
            let chosen_successors = successors
                .iter()
                .enumerate()
                .filter(|(i, _)| self.chosen.contains(*i))
                .map(|(_, s)| s)
                .collect::<Vec<_>>();
            format!(
                "{:?} -> {{ {} }}",
                self.from,
                chosen_successors
                    .iter()
                    .map(|s| format!("{s:?}"))
                    .join(", ")
            )
        }
    }
}

#[deprecated(note = "Use `ValidityConditions` instead")]
pub type PathConditions = ValidityConditions;

/// Validity conditions describing the control-flow paths for which a given edge
/// in the PCG applies.
#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct ValidityConditions(SmallVec<[BranchChoices; 8]>);

impl Default for ValidityConditions {
    fn default() -> Self {
        Self(SmallVec::new())
    }
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for ValidityConditions {
    fn to_json(&self, _ctxt: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        todo!()
    }
}

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for ValidityConditions {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        self.all_branch_choices()
            .map(|bc| bc.to_short_string(ctxt))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn effective_successors(from: BasicBlock, body: &mir::Body<'_>) -> Vec<BasicBlock> {
    let terminator = body.basic_blocks[from].terminator();
    match terminator.kind {
        mir::TerminatorKind::Call { target, .. } => target.into_iter().collect(),
        mir::TerminatorKind::Drop { target, .. } | mir::TerminatorKind::Assert { target, .. } => {
            vec![target]
        }
        mir::TerminatorKind::FalseUnwind { real_target, .. }
        | mir::TerminatorKind::FalseEdge { real_target, .. } => {
            vec![real_target]
        }
        _ => terminator.successors().collect(),
    }
}

impl ValidityConditions {
    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn new() -> Self {
        Self(SmallVec::new())
    }

    /// Returns an iterator over the [`BranchChoices`] for the validity conditions.
    /// Each [`BranchChoices`] corresponds to a unique block `b` for which some
    /// of `b`'s successors are *not* valid.
    ///
    /// Validity conditions are valid for a path if for each pair (b, b') in the
    /// path, either:
    /// - There is no branch choice for `b`
    /// - `b'` is in the set of valid successors defined by the
    ///   [`BranchChoices`] for `b`
    pub fn all_branch_choices(&self) -> impl Iterator<Item = &BranchChoices> {
        self.0.iter()
    }

    fn branch_choices_for(&mut self, from: BasicBlock) -> Option<&mut BranchChoices> {
        self.0.iter_mut().find(|c| c.from == from)
    }

    fn delete_branch_choices(&mut self, from: BasicBlock) {
        self.0.retain(|c| c.from != from);
    }

    pub(crate) fn join(&mut self, other: &Self, body: &mir::Body<'_>) -> bool {
        let mut changed = false;
        for other_branch_choices in other.all_branch_choices() {
            if let Some(existing) = self.branch_choices_for(other_branch_choices.from) {
                match existing.join(other_branch_choices, body) {
                    BranchChoicesJoinResult::CoversAllChoices => {
                        self.delete_branch_choices(other_branch_choices.from);
                        changed = true;
                    }
                    BranchChoicesJoinResult::Changed => {
                        changed = true;
                    }
                    BranchChoicesJoinResult::Unchanged => {}
                }
            }
        }
        changed
    }

    pub(crate) fn insert(&mut self, pc: PathCondition, body: &mir::Body<'_>) -> bool {
        tracing::debug!("inserting pc for {:?} -> {:?}", pc.from, pc.to);
        let successors = effective_successors(pc.from, body);
        if successors.len() == 1 {
            return false;
        }
        debug_assert!(
            self.branch_choices_for(pc.from).is_none(),
            "While inserting {:?}, expected no branch choices for {:?}, got {:?}",
            pc,
            pc.from,
            self.branch_choices_for(pc.from)
        );
        let bc_index = self
            .all_branch_choices()
            .enumerate()
            .find(|(_, bc)| bc.from > pc.from)
            .map(|(i, _)| i)
            .unwrap_or(self.all_branch_choices().count());
        let mut bc = BranchChoices::new(pc.from, successors.len());
        bc.insert(successors.iter().position(|s| *s == pc.to).unwrap());
        self.0.insert(bc_index, bc);
        tracing::debug!("After insert, {:?}", self);
        true
    }
}

impl ValidityConditions {
    pub fn valid_for_path(&self, path: &[BasicBlock], body: &mir::Body<'_>) -> bool {
        let get_successor_of_block_in_path = |block: BasicBlock| {
            let block_pos = path.iter().position(|b| *b == block);
            if let Some(block_pos) = block_pos {
                if block_pos == path.len() - 1 {
                    None
                } else {
                    Some(path[block_pos + 1])
                }
            } else {
                None
            }
        };

        for pc in self.all_branch_choices() {
            if let Some(choice) = get_successor_of_block_in_path(pc.from)
                && !pc.includes_successor(choice, body)
            {
                return false;
            }
        }
        true
    }
}
