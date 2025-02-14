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

use crate::{
    rustc_interface::{
        borrowck::consumers::{
            self, BorrowSet, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext,
        },
        dataflow::Analysis,
        index::{Idx, IndexVec},
        middle::{
            mir::{
                BasicBlock, Body, Location, Promoted, Statement, Terminator, TerminatorEdges,
                START_BLOCK,
            },
            ty::{self, GenericArgsRef, TyCtxt},
        },
    },
    BodyAndBorrows,
};

use crate::{
    borrows::engine::BorrowsEngine,
    free_pcs::{engine::FpcsEngine, CapabilityKind},
    utils::PlaceRepacker,
};

use super::{domain::PlaceCapabilitySummary, DataflowStmtPhase, DotGraphs, EvalStmtPhase};

#[rustversion::since(2024-10-14)]
type OutputFacts = Box<PoloniusOutput>;

#[rustversion::nightly(2024-09-14)]
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

impl<'tcx> From<consumers::BodyWithBorrowckFacts<'tcx>> for BodyWithBorrowckFacts<'tcx> {
    fn from(value: consumers::BodyWithBorrowckFacts<'tcx>) -> Self {
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

pub(crate) struct PCGContext<'mir, 'tcx> {
    pub(crate) rp: PlaceRepacker<'mir, 'tcx>,
    pub(crate) borrow_set: &'mir BorrowSet<'tcx>,
    pub(crate) region_inference_context: &'mir RegionInferenceContext<'tcx>,
    #[allow(dead_code)]
    pub(crate) output_facts: Option<OutputFacts>,
}

impl<'mir, 'tcx> PCGContext<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        mir: &'mir Body<'tcx>,
        borrow_set: &'mir BorrowSet<'tcx>,
        region_inference_context: &'mir RegionInferenceContext<'tcx>,
        output_facts: Option<OutputFacts>,
    ) -> Self {
        let rp = PlaceRepacker::new(mir, tcx);
        Self {
            rp,
            borrow_set,
            region_inference_context,
            output_facts,
        }
    }
}

pub struct PCGEngine<'a, 'tcx> {
    pub(crate) cgx: Rc<PCGContext<'a, 'tcx>>,
    pub(crate) fpcs: FpcsEngine<'a, 'tcx>,
    pub(crate) borrows: BorrowsEngine<'a, 'tcx>,
    debug_output_dir: Option<String>,
    dot_graphs: IndexVec<BasicBlock, Rc<RefCell<DotGraphs>>>,
    curr_block: Cell<BasicBlock>,
}
impl<'a, 'tcx> PCGEngine<'a, 'tcx> {
    fn initialize(&self, state: &mut PlaceCapabilitySummary<'a, 'tcx>, block: BasicBlock) {
        if let Some(existing_block) = state.block {
            assert!(existing_block == block);
            return;
        }
        state.set_block(block);
        state.set_dot_graphs(self.dot_graphs[block].clone());
        assert!(state.is_initialized());
    }

    pub(crate) fn new(cgx: PCGContext<'a, 'tcx>, debug_output_dir: Option<String>) -> Self {
        if let Some(dir_path) = &debug_output_dir {
            if std::path::Path::new(dir_path).exists() {
                std::fs::remove_dir_all(dir_path).expect("Failed to delete directory contents");
            }
            create_dir_all(&dir_path).expect("Failed to create directory for DOT files");
        }
        let dot_graphs = IndexVec::from_fn_n(
            |_| Rc::new(RefCell::new(DotGraphs::new())),
            cgx.rp.body().basic_blocks.len(),
        );
        let fpcs = FpcsEngine(cgx.rp);
        let borrows = BorrowsEngine::new(
            cgx.rp.tcx(),
            cgx.rp.body(),
            None, // TODO
                  // cgx.output_facts.as_ref().map(|o| o.as_ref()),
        );
        Self {
            cgx: Rc::new(cgx),
            dot_graphs,
            fpcs,
            borrows,
            debug_output_dir,
            curr_block: Cell::new(START_BLOCK),
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
}

impl<'a, 'tcx> Analysis<'tcx> for PCGEngine<'a, 'tcx> {
    type Domain = PlaceCapabilitySummary<'a, 'tcx>;
    const NAME: &'static str = "pcs";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        let block = self.curr_block.get();
        let (block, dot_graphs) = if block.as_usize() < body.basic_blocks.len() {
            self.curr_block.set(block.plus(1));
            (Some(block), Some(self.dot_graphs[block].clone()))
        } else {
            // For results cursor, don't set block
            (None, None)
        };
        PlaceCapabilitySummary::new(
            self.cgx.clone(),
            block,
            self.debug_output_dir.clone(),
            dot_graphs,
        )
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        self.curr_block.set(START_BLOCK);
        state.pcg_mut().initialize_as_start_block();
    }
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        if state.has_error() {
            return;
        }
        self.initialize(state, location.block);
        self.fpcs
            .apply_before_statement_effect(state.owned_pcg_mut(), statement, location);
        self.borrows
            .apply_before_statement_effect(state.borrow_pcg_mut(), statement, location);

        let pcg = state.pcg_mut();

        let borrows = pcg.borrow.data.states.post_main.frozen_graph();

        // Restore capabilities for owned places that were previously lent out
        // but are now no longer borrowed.
        for cap in pcg.owned.post_operands_mut().iter_mut() {
            match cap {
                crate::free_pcs::CapabilityLocal::Unallocated => {}
                crate::free_pcs::CapabilityLocal::Allocated(capability_projections) => {
                    for (root, kind) in capability_projections.iter_mut() {
                        if !borrows.contains((*root).into(), self.cgx.rp) {
                            if kind.is_read() || kind.is_lent_exclusive() {
                                *kind = CapabilityKind::Exclusive;
                            }
                        }
                    }
                }
            }
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
        if state.has_error() {
            return;
        }
        self.fpcs
            .apply_statement_effect(state.owned_pcg_mut(), statement, location);
        self.borrows
            .apply_statement_effect(state.borrow_pcg_mut(), statement, location);
        self.generate_dot_graph(state, EvalStmtPhase::PreMain, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PostMain, location.statement_index);
    }
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        if state.has_error() {
            return;
        }
        self.initialize(state, location.block);
        self.borrows
            .apply_before_terminator_effect(state.borrow_pcg_mut(), terminator, location);
        self.fpcs
            .apply_before_terminator_effect(state.owned_pcg_mut(), terminator, location);
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
        if state.has_error() {
            return terminator.edges();
        }
        self.borrows
            .apply_terminator_effect(state.borrow_pcg_mut(), terminator, location);
        self.fpcs
            .apply_terminator_effect(state.owned_pcg_mut(), terminator, location);
        self.generate_dot_graph(state, EvalStmtPhase::PreMain, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PostMain, location.statement_index);
        terminator.edges()
    }
}
