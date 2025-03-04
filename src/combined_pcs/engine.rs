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
    free_pcs::CapabilitySummary,
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
            ty::{self, GenericArgsRef, TyCtxt},
        },
    },
    utils::Place,
    BodyAndBorrows,
};

use super::{
    domain::PlaceCapabilitySummary, DataflowStmtPhase, DotGraphs, EvalStmtPhase, PCGDebugData,
};
use crate::borrow_pcg::borrow_checker::r#impl::BorrowCheckerImpl;
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

pub(crate) struct PCGContext<'mir, 'tcx> {
    pub(crate) rp: PlaceRepacker<'mir, 'tcx>,
    pub(crate) borrow_set: &'mir BorrowSet<'tcx>,
    pub(crate) region_inference_context: &'mir RegionInferenceContext<'tcx>,

    /// The initial capability summary for all blocks. We use an RC'd pointer to
    /// avoid copying the capability summary for each block (which can be large
    /// if the function has many locals)
    pub(crate) init_capability_summary: Rc<CapabilitySummary<'tcx>>,
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
        let init_capability_summary = Rc::new(CapabilitySummary::default(rp.local_count()));
        Self {
            rp,
            borrow_set,
            region_inference_context,
            init_capability_summary,
            output_facts,
        }
    }
}

struct PCGEngineDebugData {
    debug_output_dir: String,
    dot_graphs: IndexVec<BasicBlock, Rc<RefCell<DotGraphs>>>,
}

pub struct PCGEngine<'a, 'tcx> {
    pub(crate) cgx: Rc<PCGContext<'a, 'tcx>>,
    pub(crate) fpcs: FpcsEngine<'a, 'tcx>,
    pub(crate) borrows: BorrowsEngine<'a, 'tcx>,
    borrow_checker: BorrowCheckerImpl<'a, 'tcx>,
    debug_data: Option<PCGEngineDebugData>,
    curr_block: Cell<BasicBlock>,
    pub(crate) reachable_blocks: BitSet<BasicBlock>,
}
impl<'a, 'tcx> PCGEngine<'a, 'tcx> {
    pub(crate) fn edges_to_analyze<'mir>(
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

    pub(crate) fn successor_blocks<'mir>(terminator: &'mir Terminator<'tcx>) -> Vec<BasicBlock> {
        match Self::edges_to_analyze(terminator) {
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

    pub(crate) fn new(cgx: PCGContext<'a, 'tcx>, debug_output_dir: Option<String>) -> Self {
        let debug_data = debug_output_dir.map(|dir_path| {
            if std::path::Path::new(&dir_path).exists() {
                std::fs::remove_dir_all(&dir_path).expect("Failed to delete directory contents");
            }
            create_dir_all(&dir_path).expect("Failed to create directory for DOT files");
            let dot_graphs = IndexVec::from_fn_n(
                |_| Rc::new(RefCell::new(DotGraphs::new())),
                cgx.rp.body().basic_blocks.len(),
            );
            PCGEngineDebugData {
                debug_output_dir: dir_path.clone(),
                dot_graphs,
            }
        });
        let fpcs = FpcsEngine {
            repacker: cgx.rp,
            init_capability_summary: cgx.init_capability_summary.clone(),
        };
        let borrows = BorrowsEngine::new(
            cgx.rp.tcx(),
            cgx.rp.body(),
            None, // TODO
                  // cgx.output_facts.as_ref().map(|o| o.as_ref()),
        );
        let cgx = Rc::new(cgx);
        let mut reachable_blocks = BitSet::new_empty(cgx.rp.body().basic_blocks.len());
        reachable_blocks.insert(START_BLOCK);
        Self {
            reachable_blocks,
            cgx: cgx.clone(),
            fpcs,
            borrows,
            debug_data,
            curr_block: Cell::new(START_BLOCK),
            borrow_checker: BorrowCheckerImpl::new(
                cgx.rp,
                cgx.region_inference_context,
                cgx.borrow_set,
            ),
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
            self.cgx.clone(),
            self.borrow_checker.clone(),
            block,
            debug_data,
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
        if state.has_error() || !self.reachable_blocks.contains(location.block) {
            return;
        }
        self.initialize(state, location.block);
        self.fpcs
            .apply_before_statement_effect(state.owned_pcg_mut(), statement, location);
        self.borrows
            .apply_before_statement_effect(state.borrow_pcg_mut(), statement, location);

        let pcg = state.pcg_mut();

        let borrows = pcg.borrow.data.states[EvalStmtPhase::PostMain].frozen_graph();

        // Restore capabilities for owned places that were previously lent out
        // but are now no longer borrowed.
        for cap in pcg.owned.post_operands_mut().iter_mut() {
            match cap {
                crate::free_pcs::CapabilityLocal::Unallocated => {}
                crate::free_pcs::CapabilityLocal::Allocated(capability_projections) => {
                    let places: Vec<Place<'tcx>> =
                        capability_projections.iter().map(|(p, _)| *p).collect();
                    for p in places {
                        if !borrows.contains(p.into(), self.cgx.rp)
                            && capability_projections[&p].is_read()
                            && capability_projections.is_leaf(p)
                        {
                            capability_projections.insert(p, CapabilityKind::Exclusive);
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
        if state.has_error() || !self.reachable_blocks.contains(location.block) {
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
        let edges = Self::edges_to_analyze(terminator);
        if state.has_error() || !self.reachable_blocks.contains(location.block) {
            return edges;
        } else {
            for block in Self::successor_blocks(terminator) {
                self.reachable_blocks.insert(block);
            }
        }
        self.borrows
            .apply_terminator_effect(state.borrow_pcg_mut(), terminator, location);
        self.fpcs
            .apply_terminator_effect(state.owned_pcg_mut(), terminator, location);
        self.generate_dot_graph(state, EvalStmtPhase::PreMain, location.statement_index);
        self.generate_dot_graph(state, EvalStmtPhase::PostMain, location.statement_index);
        edges
    }
}
