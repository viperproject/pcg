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

use itertools::Itertools;

use crate::{
    borrow_pcg::{
        action::BorrowPCGActionKind, borrow_pcg_edge::BorrowPCGEdgeLike,
        coupling_graph_constructor::BorrowCheckerInterface,
    },
    free_pcs::RepackOp,
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

    fn output_facts(&self) -> &Option<Box<PoloniusOutput>> {
        &self.output_facts
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
        let borrows = BorrowsEngine::new(
            repacker.tcx(),
            repacker.body(),
            None, // TODO
                  // cgx.output_facts.as_ref().map(|o| o.as_ref()),
        );
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
        state: &mut PlaceCapabilitySummary<'a, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let pcg = state.pcg_mut();
        let borrows = pcg.borrow.data.states[EvalStmtPhase::PostMain].frozen_graph();

        // Restore capabilities for owned places that were previously lent out
        // but are now no longer borrowed.
        for action in pcg.borrow.actions[EvalStmtPhase::PreOperands].iter() {
            if let BorrowPCGActionKind::RemoveEdge(edge) = &action.kind {
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
                        pcg.owned
                            .data
                            .unwrap_mut(EvalStmtPhase::PostMain)
                            .set_capability_if_allocated(
                                place,
                                CapabilityKind::Exclusive,
                                self.repacker,
                            );
                    }
                }
            }
        }
        let mut extra_ops = vec![];
        let fpcg_post_state = pcg.owned.data.unwrap_mut(EvalStmtPhase::PostMain);
        for caps in fpcg_post_state.capability_projections() {
            let leaves = caps.leaves(self.repacker);

            for place in leaves {
                if caps.get_capability(place) == Some(CapabilityKind::Read)
                    && !borrows.contains(place.into(), self.repacker)
                {
                    caps.set_capability(place, CapabilityKind::Exclusive, self.repacker);
                }
            }

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
                    tracing::debug!("Collapsing {:?} to {:?}", expansion_places[0], base);
                    extra_ops.extend(caps.collapse(base, self.repacker).unwrap());
                }
            }
        }
        Ok(extra_ops)
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
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        if let Some(error) = state.error() {
            self.record_error_if_first(error);
            return;
        }
        if self.reachable_blocks.contains(location.block) {
            state.reachable = true;
        } else {
            return;
        }
        self.initialize(state, location.block);
        if let Err(e) = self
            .borrows
            .prepare_operands(state.borrow_pcg_mut(), statement, location)
        {
            self.record_error_if_first(&e);
            state.record_error(e);
            return;
        }

        state.pcg_mut().owned.data.enter_transfer_fn();
        let mut extra_ops = match self.restore_loaned_capabilities(state) {
            Ok(extra_ops) => extra_ops,
            Err(e) => {
                self.record_error_if_first(&e);
                state.record_error(e);
                return;
            }
        };

        let borrows = state.borrow_pcg().data.states[EvalStmtPhase::PreOperands].clone();
        if let Err(e) = self.fpcs.apply_before_statement_effect(
            state.owned_pcg_mut(),
            statement,
            &borrows,
            location,
        ) {
            self.record_error_if_first(&e);
            state.record_error(e);
            return;
        }
        extra_ops.append(&mut state.pcg_mut().owned.actions[EvalStmtPhase::PreOperands]);
        state.pcg_mut().owned.actions[EvalStmtPhase::PreOperands].extend(extra_ops);
        if let Err(e) = self
            .borrows
            .apply_operands(state.borrow_pcg_mut(), statement, location)
        {
            self.record_error_if_first(&e);
            state.record_error(e);
            return;
        }

        self.generate_dot_graph(state, DataflowStmtPhase::Initial, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PreOperands, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PostOperands, location.statement_index);
    }
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        if let Some(error) = state.error() {
            if self.first_error.error().is_none() {
                self.first_error.record_error(error.clone());
            }
            return;
        }
        if !self.reachable_blocks.contains(location.block) {
            return;
        }
        let borrows = state.borrow_pcg().data.states[EvalStmtPhase::PostMain].clone();
        if let Err(e) =
            self.fpcs
                .apply_statement_effect(state.owned_pcg_mut(), statement, &borrows, location)
        {
            self.record_error_if_first(&e);
            state.record_error(e);
            return;
        }
        if let Err(e) =
            self.borrows
                .apply_statement_effect(state.borrow_pcg_mut(), statement, location)
        {
            self.record_error_if_first(&e);
            state.record_error(e);
            return;
        }
        self.generate_dot_graph(state, EvalStmtPhase::PreMain, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PostMain, location.statement_index);
    }

    #[tracing::instrument(skip(self, state, terminator), fields(def_id = ?self.repacker.body().source.def_id()))]
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        if let Some(error) = state.error() {
            if self.first_error.error().is_none() {
                self.first_error.record_error(error.clone());
            }
            return;
        }
        if self.reachable_blocks.contains(location.block) {
            state.reachable = true;
        } else {
            return;
        }
        self.initialize(state, location.block);
        if let Err(e) = self.borrows.apply_before_terminator_effect(
            state.borrow_pcg_mut(),
            terminator,
            location,
        ) {
            self.record_error_if_first(&e);
            state.record_error(e);
            return;
        }
        let borrows = state.borrow_pcg().data.states[EvalStmtPhase::PostOperands].clone();
        state.pcg_mut().owned.data.enter_transfer_fn();
        let mut extra_ops = match self.restore_loaned_capabilities(state) {
            Ok(extra_ops) => extra_ops,
            Err(e) => {
                self.record_error_if_first(&e);
                state.record_error(e);
                return;
            }
        };
        if let Err(e) = self.fpcs.apply_before_terminator_effect(
            state.owned_pcg_mut(),
            terminator,
            &borrows,
            location,
        ) {
            self.record_error_if_first(&e);
            state.record_error(e);
            return;
        }
        extra_ops.append(&mut state.pcg_mut().owned.actions[EvalStmtPhase::PreOperands]);
        state.pcg_mut().owned.actions[EvalStmtPhase::PreOperands].extend(extra_ops);
        self.generate_dot_graph(state, DataflowStmtPhase::Initial, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PreOperands, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PostOperands, location.statement_index);
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let edges = edges_to_analyze(terminator);
        if state.has_error() || !self.reachable_blocks.contains(location.block) {
            return edges;
        } else {
            for block in successor_blocks(terminator) {
                self.reachable_blocks.insert(block);
            }
        }
        if let Err(e) =
            self.borrows
                .apply_terminator_effect(state.borrow_pcg_mut(), terminator, location)
        {
            self.record_error_if_first(&e);
            state.record_error(e);
            return edges;
        }
        let borrows = state.borrow_pcg().data.states[EvalStmtPhase::PostMain].clone();
        if let Err(e) =
            self.fpcs
                .apply_terminator_effect(state.owned_pcg_mut(), terminator, &borrows, location)
        {
            self.record_error_if_first(&e);
            state.record_error(e);
            return edges;
        }
        self.generate_dot_graph(state, EvalStmtPhase::PostMain, location.statement_index);
        edges
    }
}
