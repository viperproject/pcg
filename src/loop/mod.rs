//! Loop Analysis Utilities
//!
// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod loop_set;

use crate::{
    r#loop::loop_set::LoopSet,
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::mir::{self, BasicBlock, Body, START_BLOCK},
    },
    utils::{
        data_structures::{HashMap, HashSet},
        visitor::FallableVisitor,
        Place,
    },
    validity_checks_enabled,
};

#[derive(Debug)]
pub struct LoopAnalysis {
    /// Tracks the loops that each basic block is in.
    bb_data: IndexVec<BasicBlock, LoopSet>,
    /// Identifies the head of each loop.
    loop_heads: IndexVec<LoopId, BasicBlock>,
}

impl LoopAnalysis {
    pub fn find_loops(body: &Body) -> Self {
        let mut analysis = LoopAnalysis {
            bb_data: IndexVec::from_elem_n(LoopSet::new(), body.basic_blocks.len()),
            loop_heads: IndexVec::new(),
        };

        let mut visited_bbs: IndexVec<BasicBlock, bool> =
            IndexVec::from_elem_n(false, body.basic_blocks.len());

        let mut loop_head_bb_index: IndexVec<BasicBlock, LoopId> =
            IndexVec::from_elem_n(NO_LOOP, body.basic_blocks.len());
        let postorder_blocks = body.basic_blocks.reverse_postorder().iter().copied().rev();
        for bb in postorder_blocks {
            for succ in body.basic_blocks[bb].terminator().successors() {
                if visited_bbs[succ] {
                    // Merge in loops of this succ
                    assert_ne!(bb, succ);
                    let other = analysis.bb_data[succ].clone();
                    let data = &mut analysis.bb_data[bb];
                    data.merge(&other);
                    // If `succ` is a loop head, we are no longer in that loop
                    let loop_idx = loop_head_bb_index[succ];
                    if loop_idx != NO_LOOP {
                        assert_eq!(analysis.loop_heads[loop_idx], succ);
                        data.remove(loop_idx);
                    }
                } else {
                    // Create new loop
                    let loop_idx = &mut loop_head_bb_index[succ];
                    if *loop_idx == NO_LOOP {
                        *loop_idx = LoopId::new(analysis.loop_heads.len());
                        analysis.loop_heads.push(succ);
                    }
                    analysis.bb_data[bb].add(*loop_idx);
                }
            }
            visited_bbs[bb] = true;
        }
        if validity_checks_enabled() {
            analysis.consistency_check();
        }
        analysis
    }
    pub fn in_loop(&self, bb: BasicBlock, l: LoopId) -> bool {
        self.bb_data[bb].contains(l)
    }

    /// Returns an iterator over the loops that `bb` is in.
    pub fn loops(&self, bb: BasicBlock) -> impl DoubleEndedIterator<Item = LoopId> + '_ {
        self.bb_data[bb].iter()
    }

    /// Returns the number of loops that `bb` is in.
    pub fn loop_depth(&self, bb: BasicBlock) -> usize {
        self.loops(bb).count()
    }
    pub fn loop_nest_depth(&self, l: LoopId) -> usize {
        self.loop_depth(self[l]) - 1
    }
    /// Returns the loop which contains `bb` as well as all other loops of `bb`.
    pub fn outermost_loop(&self, bb: BasicBlock) -> Option<LoopId> {
        self.loops(bb).min_by_key(|l| self.loop_nest_depth(*l))
    }
    /// Returns the loop which contains `bb` but no other loops of `bb`.
    pub fn innermost_loop(&self, bb: BasicBlock) -> Option<LoopId> {
        self.loops(bb).max_by_key(|l| self.loop_nest_depth(*l))
    }

    /// If `bb` is a loop head, return the loop for which it is the head.
    pub fn loop_head_of(&self, bb: BasicBlock) -> Option<LoopId> {
        self.loops(bb).find(|l| self[*l] == bb)
    }

    fn consistency_check(&self) {
        // Start block can be in a maximum of one loop, of which it is the head
        let mut start_loops: Vec<_> = self.loops(START_BLOCK).collect();
        if let Some(l) = start_loops.pop() {
            assert_eq!(self[l], START_BLOCK);
        }
        assert!(start_loops.is_empty());
        // A bb can only be the loop head of a single loop
        for lh in &self.loop_heads {
            assert_eq!(
                self.loop_heads.iter().filter(|other| *other == lh).count(),
                1
            );
        }
    }
}

impl std::ops::Index<LoopId> for LoopAnalysis {
    type Output = BasicBlock;
    fn index(&self, index: LoopId) -> &Self::Output {
        &self.loop_heads[index]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct LoopId(usize);
impl Idx for LoopId {
    fn new(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}
const NO_LOOP: LoopId = LoopId(usize::MAX);

#[derive(Clone)]
pub(crate) struct LoopPlaceUsageAnalysis<'tcx> {
    /// This map contains, for each loop head, the set of places that are used in the loop.
    ///
    /// Note that if the loop does not use any places, there will still be an
    /// entry in this table (the corresponding value will be an empty set).
    /// Accordingly, this data structure also can be used to check whether a
    /// block is a loop head.
    loop_used_places: HashMap<BasicBlock, HashSet<Place<'tcx>>>,
}

struct UsageVisitor<'tcx> {
    used_places: HashSet<Place<'tcx>>,
}

impl<'tcx> UsageVisitor<'tcx> {
    fn new() -> Self {
        Self {
            used_places: HashSet::default(),
        }
    }
}

impl<'tcx> FallableVisitor<'tcx> for UsageVisitor<'tcx> {
    fn visit_place_fallable(
        &mut self,
        place: Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) -> Result<(), crate::pcg::PcgError> {
        self.used_places.insert(place);
        Ok(())
    }
}

impl<'tcx> LoopPlaceUsageAnalysis<'tcx> {
    pub(crate) fn is_loop_head(&self, block: BasicBlock) -> bool {
        self.loop_used_places.contains_key(&block)
    }

    pub(crate) fn new(body: &Body<'tcx>, analysis: &LoopAnalysis) -> Self {
        let mut used_places = IndexVec::from_elem_n(HashSet::default(), body.basic_blocks.len());
        for (bb_idx, bb) in body.basic_blocks.iter().enumerate() {
            let mut usage = UsageVisitor::new();
            for (idx, stmt) in bb.statements.iter().enumerate() {
                usage
                    .visit_statement_fallable(
                        stmt,
                        mir::Location {
                            block: bb_idx.into(),
                            statement_index: idx,
                        },
                    )
                    .unwrap();
            }
            used_places[bb_idx.into()] = usage.used_places;
        }

        let mut loop_used_places: HashMap<BasicBlock, HashSet<Place<'tcx>>> = HashMap::default();
        for (loop_id, loop_head) in analysis.loop_heads.iter_enumerated() {
            tracing::info!("loop head: {:?}", loop_head);
            loop_used_places.insert(*loop_head, HashSet::default());
            for (bb_idx, _) in body.basic_blocks.iter_enumerated() {
                if analysis.in_loop(bb_idx, loop_id) {
                    loop_used_places
                        .get_mut(loop_head)
                        .unwrap()
                        .extend(used_places[bb_idx].iter().copied());
                }
            }
        }
        Self { loop_used_places }
    }

    /// Returns the set of places that are used in the loop with head `block`.
    ///
    /// Returns `None` if `block` is not a loop head.
    /// If `block` is a loop head, but the loop does not use any places, this
    /// will return an empty set.
    pub(crate) fn get_used_places(&self, block: BasicBlock) -> Option<&HashSet<Place<'tcx>>> {
        self.loop_used_places.get(&block)
    }
}
