//! Loop Analysis Utilities
//!
// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod loop_set;

use derive_more::{Deref, DerefMut};
use itertools::Itertools;

use crate::{
    // borrow_checker::BorrowCheckerInterface,
    compute_fixpoint,
    r#loop::loop_set::LoopSet,
    rustc_interface::{
        dataflow::{Analysis, AnalysisEngine},
        index::{Idx, IndexVec},
        middle::{
            mir::{
                self, BasicBlock, Body, START_BLOCK,
                visit::{MutatingUseContext, PlaceContext},
            },
            ty,
        },
        mir_dataflow::{Forward, JoinSemiLattice, fmt::DebugWithContext},
    },
    utils::{
        CompilerCtxt, Place, data_structures::HashMap, display::DisplayWithCompilerCtxt,
        visitor::FallableVisitor,
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

#[derive(Clone, Debug, Deref, DerefMut, PartialEq, Eq)]
struct LoopPlaceUsageDomain<'tcx> {
    used_places: PlaceUsages<'tcx>,
}

impl JoinSemiLattice for PlaceUsages<'_> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for other_place_usage in other.iter() {
            changed |= self.update(other_place_usage.place, other_place_usage.usage);
        }
        changed
    }
}

impl JoinSemiLattice for LoopPlaceUsageDomain<'_> {
    fn join(&mut self, other: &Self) -> bool {
        self.used_places.join(&other.used_places)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub(crate) enum PlaceUsageType {
    Read,
    Mutate,
}

impl Ord for PlaceUsageType {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (PlaceUsageType::Read, PlaceUsageType::Read) => std::cmp::Ordering::Equal,
            (PlaceUsageType::Read, PlaceUsageType::Mutate) => std::cmp::Ordering::Less,
            (PlaceUsageType::Mutate, PlaceUsageType::Read) => std::cmp::Ordering::Greater,
            (PlaceUsageType::Mutate, PlaceUsageType::Mutate) => std::cmp::Ordering::Equal,
        }
    }
}

impl PartialOrd for PlaceUsageType {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl JoinSemiLattice for PlaceUsageType {
    fn join(&mut self, other: &Self) -> bool {
        match (*self, *other) {
            (PlaceUsageType::Read, PlaceUsageType::Mutate) => {
                *self = PlaceUsageType::Mutate;
                true
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct PlaceUsage<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) usage: PlaceUsageType,
}

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for PlaceUsage<'tcx> {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        format!("{}: {:?}", self.place.to_short_string(ctxt), self.usage)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(crate) struct PlaceUsages<'tcx>(HashMap<Place<'tcx>, PlaceUsageType>);

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for PlaceUsages<'tcx> {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        self.0
            .iter()
            .map(|(p, usage)| format!("{}: {:?}", p.to_short_string(ctxt), usage))
            .join("\n")
    }
}

impl<'tcx> PlaceUsages<'tcx> {
    pub(crate) fn iter_places(&self) -> impl Iterator<Item = Place<'tcx>> + '_ {
        self.0.keys().copied()
    }

    pub(crate) fn contains(&self, place: Place<'tcx>) -> bool {
        self.0.contains_key(&place)
    }

    pub(crate) fn joined_with(&self, other: &Self) -> Self {
        let mut clone = self.clone();
        clone.join(other);
        clone
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn usages_where(
        &self,
        predicate: impl Fn(PlaceUsage<'tcx>) -> bool,
    ) -> PlaceUsages<'tcx> {
        let mut clone = self.clone();
        clone.0.retain(|p, usage| {
            predicate(PlaceUsage {
                place: *p,
                usage: *usage,
            })
        });
        clone
    }

    #[must_use]
    fn update(&mut self, place: Place<'tcx>, usage: PlaceUsageType) -> bool {
        if let Some(existing_usage) = self.0.get(&place) {
            if usage == PlaceUsageType::Mutate && existing_usage == &PlaceUsageType::Read {
                self.0.insert(place, PlaceUsageType::Mutate);
                false
            } else {
                false
            }
        } else {
            self.0.insert(place, usage);
            true
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = PlaceUsage<'tcx>> + '_ {
        self.0.iter().map(|(p, usage)| PlaceUsage {
            place: *p,
            usage: *usage,
        })
    }
}

#[derive(Clone)]
pub(crate) struct LoopPlaceUsageAnalysis<'tcx> {
    /// This map contains, for each loop head, the set of places that are used in the loop.
    ///
    /// Note that if the loop does not use any places, there will still be an
    /// entry in this table (the corresponding value will be an empty set).
    /// Accordingly, this data structure also can be used to check whether a
    /// block is a loop head.
    loop_used_places: HashMap<BasicBlock, PlaceUsages<'tcx>>,
}

struct UsageVisitor<'a, 'tcx> {
    used_places: &'a mut LoopPlaceUsageDomain<'tcx>,
}

impl<'a, 'tcx> UsageVisitor<'a, 'tcx> {
    fn new(used_places: &'a mut LoopPlaceUsageDomain<'tcx>) -> Self {
        Self { used_places }
    }
}

impl<'tcx> FallableVisitor<'tcx> for UsageVisitor<'_, 'tcx> {
    fn visit_place_fallable(
        &mut self,
        place: Place<'tcx>,
        context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) -> Result<(), crate::error::PcgError> {
        match context {
            PlaceContext::MutatingUse(MutatingUseContext::Projection) => {}
            PlaceContext::MutatingUse(_) => {
                let _ = self.used_places.update(place, PlaceUsageType::Mutate);
            }
            PlaceContext::NonMutatingUse(_) => {
                let _ = self.used_places.update(place, PlaceUsageType::Read);
            }
            PlaceContext::NonUse(_) => {}
        }
        Ok(())
    }
}

struct SingleLoopAnalysis<'loops> {
    loop_id: LoopId,
    loop_analysis: &'loops LoopAnalysis,
}

impl<'tcx> Analysis<'tcx> for SingleLoopAnalysis<'_> {
    type Domain = LoopPlaceUsageDomain<'tcx>;
    type Direction = Forward;

    const NAME: &'static str = "SingleLoopAnalysis";

    fn bottom_value(&self, _body: &mir::Body<'tcx>) -> Self::Domain {
        LoopPlaceUsageDomain {
            used_places: PlaceUsages::default(),
        }
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {}

    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        if self.loop_analysis.in_loop(location.block, self.loop_id) {
            let mut visitor = UsageVisitor::new(state);
            visitor
                .visit_statement_fallable(statement, location)
                .unwrap();
        }
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: mir::Location,
    ) -> mir::TerminatorEdges<'mir, 'tcx> {
        if self.loop_analysis.in_loop(location.block, self.loop_id) {
            let mut visitor = UsageVisitor::new(state);
            visitor
                .visit_terminator_fallable(terminator, location)
                .unwrap();
        }
        terminator.edges()
    }
}

impl DebugWithContext<AnalysisEngine<SingleLoopAnalysis<'_>>> for LoopPlaceUsageDomain<'_> {}

impl<'tcx> LoopPlaceUsageAnalysis<'tcx> {
    pub(crate) fn is_loop_head(&self, block: BasicBlock) -> bool {
        self.loop_used_places.contains_key(&block)
    }

    pub(crate) fn new(tcx: ty::TyCtxt<'tcx>, body: &Body<'tcx>, analysis: &LoopAnalysis) -> Self {
        let mut loop_used_places: HashMap<BasicBlock, PlaceUsages<'tcx>> = HashMap::default();
        for (loop_id, loop_head) in analysis.loop_heads.iter_enumerated() {
            let analysis = SingleLoopAnalysis {
                loop_id,
                loop_analysis: analysis,
            };
            let results = compute_fixpoint(AnalysisEngine(analysis), tcx, body);
            let mut cursor = results.into_results_cursor(body);
            cursor.seek_to_block_start(*loop_head);
            loop_used_places.insert(*loop_head, cursor.get().used_places.clone());
        }
        Self { loop_used_places }
    }

    /// Returns the set of places that are used in the loop with head `block`.
    ///
    /// Returns `None` if `block` is not a loop head.
    /// If `block` is a loop head, but the loop does not use any places, this
    /// will return an empty set.
    pub(crate) fn get_used_places(&self, block: BasicBlock) -> Option<&PlaceUsages<'tcx>> {
        self.loop_used_places.get(&block)
    }
}
