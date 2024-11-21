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

use rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{self, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext},
    },
    dataflow::{impls::MaybeLiveLocals, Analysis, AnalysisDomain, Results},
    index::{Idx, IndexVec},
    middle::{
        mir::{
            BasicBlock, Body, CallReturnPlaces, Location, PlaceElem, Promoted, Statement,
            Terminator, TerminatorEdges, START_BLOCK,
        },
        ty::{self, GenericArgsRef, ParamEnv, TyCtxt},
    },
};

use crate::{
    borrows::{
        domain::{AbstractionType, MaybeOldPlace, MaybeRemotePlace},
        engine::BorrowsEngine,
        region_projection_member::RegionProjectionMember,
    },
    free_pcs::{engine::FpcsEngine, CapabilityKind},
    rustc_interface,
    utils::PlaceRepacker,
};

use super::{domain::PlaceCapabilitySummary, DataflowStmtPhase, DotGraphs};

#[derive(Clone)]

pub struct BodyWithBorrowckFacts<'tcx> {
    pub body: Body<'tcx>,
    pub promoted: IndexVec<Promoted, Body<'tcx>>,
    pub borrow_set: Rc<BorrowSet<'tcx>>,
    pub region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    pub location_table: Option<Rc<LocationTable>>,
    pub input_facts: Option<Box<PoloniusInput>>,
    pub output_facts: Option<Rc<PoloniusOutput>>,
}

impl<'tcx> BodyWithBorrowckFacts<'tcx> {
    pub fn monomorphize(
        self,
        tcx: ty::TyCtxt<'tcx>,
        substs: GenericArgsRef<'tcx>,
        param_env: ParamEnv<'tcx>,
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
            borrow_set: value.borrow_set,
            region_inference_context: value.region_inference_context,
            location_table: value.location_table.map(Rc::new),
            input_facts: value.input_facts,
            output_facts: value.output_facts,
        }
    }
}

pub struct PcsContext<'a, 'tcx> {
    pub rp: PlaceRepacker<'a, 'tcx>,
    pub mir: &'a BodyWithBorrowckFacts<'tcx>,
}

impl<'a, 'tcx> PcsContext<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, mir: &'a BodyWithBorrowckFacts<'tcx>) -> Self {
        let rp = PlaceRepacker::new(&mir.body, tcx);
        Self { rp, mir }
    }
}

pub struct PcsEngine<'a, 'tcx> {
    pub(crate) cgx: Rc<PcsContext<'a, 'tcx>>,
    pub(crate) fpcs: FpcsEngine<'a, 'tcx>,
    pub(crate) borrows: BorrowsEngine<'a, 'tcx>,
    maybe_live_locals: Rc<Results<'tcx, MaybeLiveLocals>>,
    debug_output_dir: Option<String>,
    dot_graphs: IndexVec<BasicBlock, Rc<RefCell<DotGraphs>>>,
    curr_block: Cell<BasicBlock>,
}
impl<'a, 'tcx> PcsEngine<'a, 'tcx> {
    fn initialize(&self, state: &mut PlaceCapabilitySummary<'a, 'tcx>, block: BasicBlock) {
        if let Some(existing_block) = state.block {
            assert!(existing_block == block);
            return;
        }
        state.set_block(block);
        state.set_dot_graphs(self.dot_graphs[block].clone());
        assert!(state.is_initialized());
    }

    pub fn new(cgx: PcsContext<'a, 'tcx>, debug_output_dir: Option<String>) -> Self {
        if let Some(dir_path) = &debug_output_dir {
            if std::path::Path::new(dir_path).exists() {
                std::fs::remove_dir_all(dir_path).expect("Failed to delete directory contents");
            }
            create_dir_all(&dir_path).expect("Failed to create directory for DOT files");
        }
        let dot_graphs = IndexVec::from_fn_n(
            |_| Rc::new(RefCell::new(DotGraphs::new())),
            cgx.mir.body.basic_blocks.len(),
        );
        let cgx = Rc::new(cgx);
        let fpcs = FpcsEngine(cgx.rp);
        let borrows = BorrowsEngine::new(
            cgx.rp.tcx(),
            cgx.rp.body(),
            cgx.mir.location_table.as_ref().unwrap(),
            cgx.mir.input_facts.as_ref().unwrap(),
            cgx.mir.borrow_set.clone(),
            cgx.mir.region_inference_context.clone(),
            cgx.mir.output_facts.as_ref().unwrap(),
        );
        let maybe_live_locals = MaybeLiveLocals
            .into_engine(cgx.rp.tcx(), cgx.rp.body())
            .iterate_to_fixpoint();
        Self {
            cgx,
            dot_graphs,
            fpcs,
            borrows,
            maybe_live_locals: Rc::new(maybe_live_locals),
            debug_output_dir,
            curr_block: Cell::new(START_BLOCK),
        }
    }

    fn generate_dot_graph(
        &self,
        state: &mut PlaceCapabilitySummary<'a, 'tcx>,
        phase: DataflowStmtPhase,
        statement_index: usize,
    ) {
        state.generate_dot_graph(phase, statement_index);
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for PcsEngine<'a, 'tcx> {
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
            self.maybe_live_locals.clone(),
        )
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        self.curr_block.set(START_BLOCK);
        state.fpcs.initialize_as_start_block();
        state.borrows.initialize_as_start_block();
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct ProjectionEdge<'tcx> {
    pub blockers: Vec<PlaceElem<'tcx>>,
    pub blocked: MaybeOldPlace<'tcx>,
}

impl<'tcx> ProjectionEdge<'tcx> {
    pub fn blocks_place(&self, place: MaybeOldPlace<'tcx>) -> bool {
        self.blocked == place
    }
    pub fn blocker_places(&self, tcx: TyCtxt<'tcx>) -> Vec<MaybeOldPlace<'tcx>> {
        self.blockers
            .iter()
            .map(|p| self.blocked.project_deeper(tcx, *p))
            .collect()
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum UnblockAction<'tcx> {
    TerminateRegionProjectionMember(RegionProjectionMember<'tcx>),
    TerminateAbstraction(Location, AbstractionType<'tcx>),
    TerminateBorrow {
        reserve_location: Location,
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
        is_mut: bool,
    },
    Collapse(MaybeOldPlace<'tcx>, Vec<MaybeOldPlace<'tcx>>),
}

impl<'a, 'tcx> Analysis<'tcx> for PcsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.initialize(state, location.block);
        self.generate_dot_graph(state, DataflowStmtPhase::Initial, location.statement_index);
        self.fpcs
            .apply_before_statement_effect(&mut state.fpcs, statement, location);
        self.borrows
            .apply_before_statement_effect(&mut state.borrows, statement, location);
        for cap in state.fpcs.post_operands.iter_mut() {
            match cap {
                crate::free_pcs::CapabilityLocal::Unallocated => {}
                crate::free_pcs::CapabilityLocal::Allocated(capability_projections) => {
                    for (root, kind) in capability_projections.iter_mut() {
                        if !state.borrows.states.after.contains(*root, self.cgx.rp) {
                            if kind.is_read() || kind.is_lent_exclusive() {
                                *kind = CapabilityKind::Exclusive;
                            }
                        }
                    }
                }
            }
        }
        self.generate_dot_graph(
            state,
            DataflowStmtPhase::BeforeStart,
            location.statement_index,
        );
        self.generate_dot_graph(
            state,
            DataflowStmtPhase::BeforeAfter,
            location.statement_index,
        );
    }
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.fpcs
            .apply_statement_effect(&mut state.fpcs, statement, location);
        self.borrows
            .apply_statement_effect(&mut state.borrows, statement, location);
        self.generate_dot_graph(state, DataflowStmtPhase::Start, location.statement_index);
        self.generate_dot_graph(state, DataflowStmtPhase::After, location.statement_index);
    }
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        self.initialize(state, location.block);
        self.generate_dot_graph(state, DataflowStmtPhase::Initial, location.statement_index);
        self.borrows
            .apply_before_terminator_effect(&mut state.borrows, terminator, location);
        self.fpcs
            .apply_before_terminator_effect(&mut state.fpcs, terminator, location);
        self.generate_dot_graph(
            state,
            DataflowStmtPhase::BeforeStart,
            location.statement_index,
        );
        self.generate_dot_graph(
            state,
            DataflowStmtPhase::BeforeAfter,
            location.statement_index,
        );
    }
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.borrows
            .apply_terminator_effect(&mut state.borrows, terminator, location);
        self.fpcs
            .apply_terminator_effect(&mut state.fpcs, terminator, location);
        self.generate_dot_graph(state, DataflowStmtPhase::Start, location.statement_index);
        self.generate_dot_graph(state, DataflowStmtPhase::After, location.statement_index);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}
