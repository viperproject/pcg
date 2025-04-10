// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cell::{Cell, RefCell},
    fs::create_dir_all,
    rc::Rc,
};

use derive_more::From;
use itertools::Itertools;

use crate::{
    borrow_pcg::{
        action::{actions::BorrowPCGActions, BorrowPCGActionKind},
        borrow_pcg_edge::BorrowPCGEdgeLike,
        coupling_graph_constructor::BorrowCheckerInterface,
        graph::frozen::FrozenGraphRef,
    },
    free_pcs::{triple::TripleWalker, CapabilitySummary, FreePlaceCapabilitySummary, RepackOp},
    rustc_interface::{
        borrowck::{
            self, BorrowSet, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext,
        },
        dataflow::Analysis,
        index::{bit_set::BitSet, Idx, IndexVec},
        middle::{
            mir::{
                self, BasicBlock, Body, Location, Promoted, Statement, Terminator, TerminatorEdges,
                START_BLOCK,
            },
            ty::{self, GenericArgsRef},
        },
    },
    utils::visitor::FallableVisitor,
    BodyAndBorrows,
};

use super::{
    domain::PlaceCapabilitySummary, DataflowStmtPhase, DotGraphs, ErrorState, EvalStmtPhase,
    PCGDebugData, PcgError,
};
use crate::{
    borrow_pcg::engine::BorrowsEngine,
    free_pcs::{engine::FpcsEngine, CapabilityKind},
    utils::PlaceRepacker,
};

#[rustversion::since(2024-10-03)]
type OutputFacts = Box<PoloniusOutput>;

#[rustversion::before(2024-10-03)]
type OutputFacts = Rc<PoloniusOutput>;

#[derive(Clone)]

pub struct BodyWithBorrowckFacts<'tcx> {
    pub body: Body<'tcx>,
    pub promoted: IndexVec<Promoted, Body<'tcx>>,
    pub borrow_set: Rc<BorrowSet<'tcx>>,
    pub region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    pub location_table: Option<Rc<LocationTable>>,
    pub input_facts: Option<Box<PoloniusInput>>,
    pub output_facts: Option<OutputFacts>,
}

impl<'tcx> BodyAndBorrows<'tcx> for BodyWithBorrowckFacts<'tcx> {
    fn body(&self) -> &Body<'tcx> {
        &self.body
    }
    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        &self.borrow_set
    }
    fn region_inference_context(&self) -> &RegionInferenceContext<'tcx> {
        &self.region_inference_context
    }

    #[rustversion::before(2024-10-03)]
    fn output_facts(&self) -> Option<Box<PoloniusOutput>> {
        self.output_facts
            .clone()
            .map(|o| Box::new(o.as_ref().clone()))
    }

    #[rustversion::since(2024-10-03)]
    fn output_facts(&self) -> Option<Box<PoloniusOutput>> {
        self.output_facts.clone()
    }

    fn location_table(&self) -> &LocationTable {
        self.location_table.as_ref().unwrap()
    }

    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts.as_ref().unwrap()
    }
}

#[rustversion::before(2024-12-14)]
type MonomorphizeEnv<'tcx> = ty::ParamEnv<'tcx>;

#[rustversion::since(2024-12-14)]
type MonomorphizeEnv<'tcx> = ty::TypingEnv<'tcx>;

impl<'tcx> BodyWithBorrowckFacts<'tcx> {
    pub fn monomorphize(
        self,
        tcx: ty::TyCtxt<'tcx>,
        substs: GenericArgsRef<'tcx>,
        param_env: MonomorphizeEnv<'tcx>,
    ) -> Self {
        let body = tcx.erase_regions(self.body.clone());
        let monomorphized_body = tcx.instantiate_and_normalize_erasing_regions(
            substs,
            param_env,
            ty::EarlyBinder::bind(body),
        );
        Self {
            body: monomorphized_body,
            promoted: self.promoted,
            borrow_set: self.borrow_set,
            region_inference_context: self.region_inference_context,
            input_facts: self.input_facts,
            location_table: self.location_table,
            output_facts: self.output_facts,
        }
    }
}

impl<'tcx> From<borrowck::BodyWithBorrowckFacts<'tcx>> for BodyWithBorrowckFacts<'tcx> {
    fn from(value: borrowck::BodyWithBorrowckFacts<'tcx>) -> Self {
        Self {
            body: value.body,
            promoted: value.promoted,
            borrow_set: value.borrow_set.into(),
            region_inference_context: value.region_inference_context.into(),
            location_table: value.location_table.map(Rc::new),
            input_facts: value.input_facts,
            output_facts: value.output_facts,
        }
    }
}

struct PCGEngineDebugData {
    debug_output_dir: String,
    dot_graphs: IndexVec<BasicBlock, Rc<RefCell<DotGraphs>>>,
}

pub struct PCGEngine<'a, 'tcx: 'a> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
    pub(crate) fpcs: FpcsEngine<'a, 'tcx>,
    pub(crate) borrows: BorrowsEngine<'a, 'tcx>,
    pub(crate) borrow_checker: Rc<dyn BorrowCheckerInterface<'a, 'tcx> + 'a>,
    debug_data: Option<PCGEngineDebugData>,
    curr_block: Cell<BasicBlock>,
    pub(crate) reachable_blocks: BitSet<BasicBlock>,
    pub(crate) first_error: ErrorState,
}
pub(crate) fn edges_to_analyze<'tcx, 'mir>(
    terminator: &'mir Terminator<'tcx>,
) -> TerminatorEdges<'mir, 'tcx> {
    match &terminator.kind {
        mir::TerminatorKind::FalseUnwind { real_target, .. } => {
            TerminatorEdges::Single(*real_target)
        }
        mir::TerminatorKind::Call { target, .. } => {
            if let Some(target) = target {
                TerminatorEdges::Single(*target)
            } else {
                TerminatorEdges::None
            }
        }
        mir::TerminatorKind::Assert { target, .. } => TerminatorEdges::Single(*target),
        mir::TerminatorKind::Drop { target, .. } => TerminatorEdges::Single(*target),
        _ => terminator.edges(),
    }
}

pub(crate) fn successor_blocks(terminator: &Terminator<'_>) -> Vec<BasicBlock> {
    match edges_to_analyze(terminator) {
        TerminatorEdges::None => vec![],
        TerminatorEdges::Single(basic_block) => vec![basic_block],
        TerminatorEdges::Double(basic_block, basic_block1) => vec![basic_block, basic_block1],
        TerminatorEdges::AssignOnReturn {
            return_, cleanup, ..
        } => {
            let mut result = vec![];
            for block in return_ {
                result.push(*block);
            }
            if let Some(cleanup) = cleanup {
                result.push(cleanup);
            }
            result
        }
        TerminatorEdges::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
    }
}

#[derive(Clone, Copy, Debug, From)]
pub(crate) enum AnalysisObject<'mir, 'tcx> {
    Statement(&'mir Statement<'tcx>),
    Terminator(&'mir Terminator<'tcx>),
}

impl<'a, 'tcx: 'a> PCGEngine<'a, 'tcx> {
    fn dot_graphs(&self, block: BasicBlock) -> Option<Rc<RefCell<DotGraphs>>> {
        self.debug_data
            .as_ref()
            .map(|data| data.dot_graphs[block].clone())
    }
    fn debug_output_dir(&self) -> Option<String> {
        self.debug_data
            .as_ref()
            .map(|data| data.debug_output_dir.clone())
    }
    fn initialize(&self, state: &mut PlaceCapabilitySummary<'a, 'tcx>, block: BasicBlock) {
        if let Some(existing_block) = state.block {
            assert!(existing_block == block);
            return;
        }
        state.set_block(block);
        if let Some(debug_data) = &self.debug_data {
            state.set_debug_data(
                debug_data.debug_output_dir.clone(),
                debug_data.dot_graphs[block].clone(),
            );
        }
        assert!(state.is_initialized());
    }

    #[tracing::instrument(skip(self, state))]
    fn analyze(
        &mut self,
        state: &mut PlaceCapabilitySummary<'a, 'tcx>,
        object: AnalysisObject<'_, 'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        if self.reachable_blocks.contains(location.block) {
            state.reachable = true;
        } else {
            return Ok(());
        }
        if let AnalysisObject::Terminator(t) = object {
            for block in successor_blocks(t) {
                self.reachable_blocks.insert(block);
            }
        }
        self.initialize(state, location.block);

        let pcg = state.pcg_mut();
        pcg.borrow.data.enter_transfer_fn();

        pcg.borrow.data.states.0.pre_operands = pcg.borrow.data.states.0.post_main.clone();

        // Handle initial borrow actions, mostly expiring borrows
        pcg.borrow.actions.pre_operands = self.borrows.analyze(
            Rc::make_mut(&mut pcg.borrow.data.states.0.pre_operands),
            self.borrow_checker.clone(),
            object,
            EvalStmtPhase::PreOperands,
            location,
        )?;

        pcg.owned.data.enter_transfer_fn();
        if !pcg.owned.data.states.0.post_main.is_some() {
            tracing::error!("post_main is not set");
            panic!("post_main is not set");
        }
        let borrows = pcg.borrow.data.states[EvalStmtPhase::PreOperands].frozen_graph();

        // Restore caps for owned places according to borrow expiry
        self.restore_loaned_capabilities(
            &mut pcg.owned,
            &borrows,
            pcg.borrow.actions.get(EvalStmtPhase::PreOperands),
            EvalStmtPhase::PostMain,
        );

        let owned = pcg.owned.data.unwrap_mut(EvalStmtPhase::PostMain);

        self.regain_exclusive_capabilities_from_read_leafs(owned, &borrows);
        let mut extra_ops = self.collapse_owned_places(owned, &borrows);

        let mut tw = TripleWalker::new(self.repacker);
        match object {
            AnalysisObject::Statement(statement) => {
                tw.visit_statement_fallable(statement, location)?;
            }
            AnalysisObject::Terminator(terminator) => {
                tw.visit_terminator_fallable(terminator, location)?;
            }
        }

        {
            let borrows = pcg.borrow.data.states[EvalStmtPhase::PreOperands].clone();

            self.fpcs
                .apply_before(&mut pcg.owned, &tw, &borrows, location)?;
        }
        extra_ops.append(&mut pcg.owned.actions[EvalStmtPhase::PreOperands]);
        pcg.owned.actions[EvalStmtPhase::PreOperands].extend(extra_ops);

        pcg.borrow.data.states.0.post_operands = pcg.borrow.data.states.0.pre_operands.clone();

        pcg.borrow.actions.post_operands = self.borrows.analyze(
            Rc::make_mut(&mut pcg.borrow.data.states.0.post_operands),
            self.borrow_checker.clone(),
            object,
            EvalStmtPhase::PostOperands,
            location,
        )?;

        // Begin by handling borrow pre_main actions

        pcg.borrow.data.states.0.pre_main = pcg.borrow.data.states.0.post_operands.clone();

        pcg.borrow.actions.pre_main = self.borrows.analyze(
            Rc::make_mut(&mut pcg.borrow.data.states.0.pre_main),
            self.borrow_checker.clone(),
            object,
            EvalStmtPhase::PreMain,
            location,
        )?;

        // Any borrows that have expired, we regain capabilities to corresponding owned places
        pcg.owned.data.states.0.pre_main = pcg.owned.data.states.0.post_operands.clone();

        self.restore_loaned_capabilities(
            &mut pcg.owned,
            &pcg.borrow.data.states[EvalStmtPhase::PreMain].frozen_graph(),
            pcg.borrow.actions.get(EvalStmtPhase::PreMain),
            EvalStmtPhase::PreMain,
        );

        // Do all of the owned effects
        let borrows = pcg.borrow.data.states[EvalStmtPhase::PreMain].clone();

        self.fpcs
            .apply_main(&mut pcg.owned, tw, &borrows, location)?;

        pcg.borrow.data.states.0.post_main = pcg.borrow.data.states.0.pre_main.clone();

        pcg.borrow.actions.post_main = self.borrows.analyze(
            Rc::make_mut(&mut pcg.borrow.data.states.0.post_main),
            self.borrow_checker.clone(),
            object,
            EvalStmtPhase::PostMain,
            location,
        )?;

        self.generate_dot_graph(state, DataflowStmtPhase::Initial, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PreOperands, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PostOperands, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PreMain, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PostMain, location.statement_index);
        Ok(())
    }

    pub(crate) fn new(
        repacker: PlaceRepacker<'a, 'tcx>,
        borrow_checker: impl BorrowCheckerInterface<'a, 'tcx> + 'a,
        debug_output_dir: Option<String>,
    ) -> Self {
        let debug_data = debug_output_dir.map(|dir_path| {
            if std::path::Path::new(&dir_path).exists() {
                std::fs::remove_dir_all(&dir_path).expect("Failed to delete directory contents");
            }
            create_dir_all(&dir_path).expect("Failed to create directory for DOT files");
            let dot_graphs = IndexVec::from_fn_n(
                |_| Rc::new(RefCell::new(DotGraphs::new())),
                repacker.body().basic_blocks.len(),
            );
            PCGEngineDebugData {
                debug_output_dir: dir_path.clone(),
                dot_graphs,
            }
        });
        let fpcs = FpcsEngine { repacker };
        let borrows = BorrowsEngine::new(repacker.tcx(), repacker.body());
        let mut reachable_blocks = BitSet::new_empty(repacker.body().basic_blocks.len());
        reachable_blocks.insert(START_BLOCK);
        Self {
            first_error: ErrorState::default(),
            reachable_blocks,
            repacker,
            fpcs,
            borrows,
            debug_data,
            curr_block: Cell::new(START_BLOCK),
            borrow_checker: Rc::new(borrow_checker),
        }
    }

    fn generate_dot_graph(
        &self,
        state: &mut PlaceCapabilitySummary<'a, 'tcx>,
        phase: impl Into<DataflowStmtPhase>,
        statement_index: usize,
    ) {
        state.generate_dot_graph(phase.into(), statement_index);
    }

    fn restore_loaned_capabilities(
        &self,
        owned: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        borrows: &FrozenGraphRef<'_, 'tcx>,
        borrow_actions: &BorrowPCGActions<'tcx>,
        owned_phase: EvalStmtPhase,
    ) {
        let owned_state = owned.data.unwrap_mut(owned_phase);

        // Restore capabilities for owned places that were previously lent out
        // but are now no longer borrowed.
        for action in borrow_actions.0.iter() {
            match &action.kind {
                BorrowPCGActionKind::MakePlaceOld(place, _) => {
                    if place.is_owned(self.repacker)
                        && owned_state.get_capability(*place) != Some(CapabilityKind::Write)
                    {
                        // A bit of an annoying hack: if the place has *no* capability (or read cap), then it's borrowed.
                        // The borrows are now going to refer to the old place, so we can regain exclusive cap here.
                        // However, the borrows graph currently reports this action even for things that aren't borrowed,
                        // (esp. for StorageDead on a place with only Write permission). So we only restore permission
                        // if the place actually has a value.
                        // TODO: We should fix this when merging owned and borrow PCG logic.
                        owned_state.set_capability_if_allocated(
                            *place,
                            CapabilityKind::Exclusive,
                            self.repacker,
                        );
                    }
                }
                BorrowPCGActionKind::RemoveEdge(edge) => {
                    for place in edge
                        .blocked_places(self.repacker)
                        .iter()
                        .flat_map(|p| p.as_current_place())
                    {
                        if place.is_owned(self.repacker)
                            && !borrows.contains(place.into(), self.repacker)
                        {
                            // It's possible that the place isn't allocated because
                            // it was already StorageDead'd. In this case it
                            // shouldn't obtain any capability.
                            // See test-files/92_http_path.rs for an example.
                            owned_state.set_capability_if_allocated(
                                place,
                                CapabilityKind::Exclusive,
                                self.repacker,
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn regain_exclusive_capabilities_from_read_leafs(
        &self,
        owned_state: &mut CapabilitySummary<'tcx>,
        borrows: &FrozenGraphRef<'_, 'tcx>,
    ) {
        for caps in owned_state.capability_projections_mut() {
            let leaves = caps.leaves(self.repacker);

            for place in leaves {
                if caps.get_capability(place) == Some(CapabilityKind::Read)
                    && !borrows.contains(place.into(), self.repacker)
                {
                    caps.set_capability(place, CapabilityKind::Exclusive, self.repacker);
                }
            }
        }
    }

    #[must_use]
    fn collapse_owned_places(
        &self,
        owned_state: &mut CapabilitySummary<'tcx>,
        borrows: &FrozenGraphRef<'_, 'tcx>,
    ) -> Vec<RepackOp<'tcx>> {
        let mut ops = vec![];
        for caps in owned_state.capability_projections_mut() {
            let mut expansions = caps
                .expansions()
                .clone()
                .into_iter()
                .sorted_by_key(|(p, _)| p.projection.len())
                .collect::<Vec<_>>();
            while let Some((base, expansion)) = expansions.pop() {
                let expansion_places = base.expansion_places(&expansion, self.repacker);
                if expansion_places
                    .iter()
                    .all(|p| !borrows.contains((*p).into(), self.repacker))
                    && let Some(candidate_cap) = caps.get_capability(expansion_places[0])
                    && expansion_places
                        .iter()
                        .all(|p| caps.get_capability(*p) == Some(candidate_cap))
                {
                    ops.extend(caps.collapse(base, self.repacker).unwrap());
                }
            }
        }
        ops
    }

    fn record_error_if_first(&mut self, error: &PcgError) {
        if self.first_error.error().is_none() {
            self.first_error.record_error(error.clone());
        }
    }
}

impl<'a, 'tcx> Analysis<'tcx> for PCGEngine<'a, 'tcx> {
    type Domain = PlaceCapabilitySummary<'a, 'tcx>;
    const NAME: &'static str = "pcs";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        let curr_block = self.curr_block.get();
        let (block, debug_data) = if curr_block.as_usize() < body.basic_blocks.len() {
            self.curr_block.set(curr_block.plus(1));
            let debug_data = self.debug_output_dir().map(|dir| PCGDebugData {
                dot_output_dir: dir,
                dot_graphs: self.dot_graphs(curr_block).unwrap(),
            });
            (Some(curr_block), debug_data)
        } else {
            // For results cursor, don't set block or consider debug data
            (None, None)
        };
        PlaceCapabilitySummary::new(
            self.repacker,
            self.borrow_checker.clone(),
            block,
            debug_data,
        )
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        self.curr_block.set(START_BLOCK);
        state.pcg_mut().initialize_as_start_block();
        state.reachable = true;
    }

    #[tracing::instrument(skip(self, state, statement))]
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        if let Some(error) = state.error() {
            self.record_error_if_first(error);
            return;
        }
        if let Err(e) = self.analyze(state, statement.into(), location) {
            self.record_error_if_first(&e);
            state.record_error(e);
        }
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let edges = edges_to_analyze(terminator);
        if let Some(error) = state.error() {
            if self.first_error.error().is_none() {
                self.first_error.record_error(error.clone());
            }
            return edges;
        }
        if let Err(e) = self.analyze(state, terminator.into(), location) {
            self.record_error_if_first(&e);
            state.record_error(e);
        }
        edges
    }
}
