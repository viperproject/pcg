// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{cell::RefCell, fs::create_dir_all, rc::Rc};

use bit_set::BitSet;
use derive_more::From;

use super::{
    DataflowStmtPhase, ErrorState, EvalStmtPhase, PcgBlockDebugVisualizationGraphs,
    domain::PcgDomain, visitor::PcgVisitor,
};
use crate::error::PcgError;
use crate::{
    BodyAndBorrows,
    pcg::{
        DataflowState, DomainDataWithCtxt, HasPcgDomainData, PcgDomainData, SymbolicCapabilityCtxt,
        ctxt::AnalysisCtxt, triple::TripleWalker,
    },
    pcg_validity_assert,
    rustc_interface::{
        borrowck::{self, BorrowSet, LocationTable, PoloniusInput, RegionInferenceContext},
        dataflow::Analysis,
        index::IndexVec,
        middle::{
            mir::{
                self, BasicBlock, Body, Location, Promoted, START_BLOCK, Statement, Terminator,
                TerminatorEdges,
            },
            ty::{self, GenericArgsRef},
        },
        mir_dataflow::{Forward, move_paths::MoveData},
    },
    utils::{AnalysisLocation, DataflowCtxt, visitor::FallableVisitor},
};
use crate::{
    pcg::{BodyAnalysis, dot_graphs::PcgDotGraphsForBlock},
    utils::{CompilerCtxt, arena::PcgArenaRef},
};

#[derive(Clone)]

pub struct BodyWithBorrowckFacts<'tcx> {
    pub body: Body<'tcx>,
    pub promoted: IndexVec<Promoted, Body<'tcx>>,
    pub borrow_set: Rc<BorrowSet<'tcx>>,
    pub region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    pub location_table: Option<Rc<LocationTable>>,
    pub input_facts: Option<Box<PoloniusInput>>,
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

    fn location_table(&self) -> &LocationTable {
        self.location_table.as_ref().unwrap()
    }

    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts.as_ref().unwrap()
    }
}

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
        }
    }
}

struct PCGEngineDebugData<'a> {
    debug_output_dir: &'a str,
    dot_graphs: IndexVec<BasicBlock, &'a RefCell<PcgDotGraphsForBlock>>,
}

type Block = usize;

pub(crate) type PcgArenaStore = bumpalo::Bump;
pub(crate) type PcgArena<'a> = &'a PcgArenaStore;

pub struct PcgEngine<'a, 'tcx: 'a> {
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
    pub(crate) symbolic_capability_ctxt: SymbolicCapabilityCtxt<'a, 'tcx>,
    debug_graphs: Option<PCGEngineDebugData<'a>>,
    body_analysis: &'a BodyAnalysis<'a, 'tcx>,
    pub(crate) reachable_blocks: BitSet<Block>,
    pub(crate) analyzed_blocks: BitSet<Block>,
    pub(crate) first_error: ErrorState,
    pub(crate) arena: PcgArena<'a>,
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

impl<'a, 'tcx: 'a> PcgEngine<'a, 'tcx> {
    fn dot_graphs(&self, block: BasicBlock) -> Option<PcgBlockDebugVisualizationGraphs<'a>> {
        self.debug_graphs.as_ref().map(|data| {
            PcgBlockDebugVisualizationGraphs::new(
                block,
                data.debug_output_dir,
                data.dot_graphs[block],
            )
        })
    }

    pub(crate) fn analysis_ctxt(&self, block: BasicBlock) -> AnalysisCtxt<'a, 'tcx> {
        AnalysisCtxt::new(
            self.ctxt,
            block,
            self.body_analysis,
            self.symbolic_capability_ctxt,
            self.arena,
            self.dot_graphs(block),
        )
    }

    fn visit_all_phases<Ctxt: DataflowCtxt<'a, 'tcx>>(
        &mut self,
        state: &mut DomainDataWithCtxt<'a, 'tcx, Ctxt>,
        object: AnalysisObject<'_, 'tcx>,
        tw: &TripleWalker<'a, 'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        let domain = &mut state.data;
        for phase in EvalStmtPhase::phases() {
            let curr = PcgArenaRef::make_mut(&mut domain.pcg.states.0[phase]);
            let analysis_location = AnalysisLocation {
                location,
                eval_stmt_phase: phase,
            };
            domain.actions[phase] =
                PcgVisitor::visit(curr, tw, analysis_location, object, state.ctxt)?;
            if let Some(next_phase) = phase.next() {
                domain.pcg.states.0[next_phase] = domain.pcg.states.0[phase].clone();
            }
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, state, object))]
    fn analyze<'obj>(
        &mut self,
        state: &mut PcgDomain<'a, 'tcx>,
        object: AnalysisObject<'obj, 'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        if !self.reachable_blocks.contains(location.block.index()) {
            return Ok(());
        }
        pcg_validity_assert!(!state.is_bottom(), "unexpected state: {:?}", state);
        if let PcgDomain::Analysis(state) = state {
            state.ensure_transfer(self.analysis_ctxt(location.block))?;

            if let AnalysisObject::Terminator(t) = object {
                for block in successor_blocks(t) {
                    self.reachable_blocks.insert(block.index());
                }
            }

            tracing::info!("Analyzing {:?}", location);
        }

        let pcg_data = state.data_mut();

        let pcg = &mut pcg_data.pcg;
        if location.statement_index != 0 {
            pcg.entry_state = pcg.states.0.post_main.clone();
        }
        pcg.states.0.pre_operands = pcg.entry_state.clone();

        let mut tw = TripleWalker::new(self.ctxt);
        match object {
            AnalysisObject::Statement(statement) => {
                tw.visit_statement_fallable(statement, location)?;
            }
            AnalysisObject::Terminator(terminator) => {
                tw.visit_terminator_fallable(terminator, location)?;
            }
        }

        match state {
            PcgDomain::Analysis(DataflowState::Transfer(state)) => {
                self.visit_all_phases(state, object, &tw, location)?
            }
            PcgDomain::Results(state) => self.visit_all_phases(state, object, &tw, location)?,
            _ => todo!(),
        }

        if let PcgDomain::Analysis(state) = state {
            let state = state.expect_transfer();
            self.analyzed_blocks.insert(location.block.index());

            state.generate_dot_graph(DataflowStmtPhase::Initial, location, state.ctxt);
            for phase in EvalStmtPhase::phases() {
                state.generate_dot_graph(phase.into(), location, state.ctxt);
            }
        }
        Ok(())
    }

    pub(crate) fn new(
        ctxt: CompilerCtxt<'a, 'tcx>,
        move_data: &'a MoveData<'tcx>,
        arena: PcgArena<'a>,
        debug_output_dir: Option<&str>,
    ) -> Self {
        let debug_data = debug_output_dir.map(|dir_path| {
            if std::path::Path::new(&dir_path).exists() {
                std::fs::remove_dir_all(dir_path).expect("Failed to delete directory contents");
            }
            create_dir_all(dir_path).expect("Failed to create directory for DOT files");
            let dot_graphs: IndexVec<BasicBlock, &'a RefCell<PcgDotGraphsForBlock>> =
                IndexVec::from_fn_n(
                    |b| {
                        let blocks: &'a RefCell<PcgDotGraphsForBlock> =
                            arena.alloc(RefCell::new(PcgDotGraphsForBlock::new(b, ctxt)));
                        blocks
                    },
                    ctxt.body().basic_blocks.len(),
                );
            PCGEngineDebugData {
                debug_output_dir: arena.alloc(dir_path.to_string()),
                dot_graphs,
            }
        });
        let mut reachable_blocks = BitSet::default();
        reachable_blocks.reserve_len(ctxt.body().basic_blocks.len());
        reachable_blocks.insert(START_BLOCK.index());
        let mut analyzed_blocks = BitSet::default();
        analyzed_blocks.reserve_len(ctxt.body().basic_blocks.len());
        Self {
            first_error: ErrorState::default(),
            reachable_blocks,
            ctxt,
            debug_graphs: debug_data,
            body_analysis: arena.alloc(BodyAnalysis::new(ctxt, move_data)),
            arena,
            symbolic_capability_ctxt: SymbolicCapabilityCtxt::new(arena),
            analyzed_blocks,
        }
    }

    fn record_error_if_first(&mut self, error: &PcgError) {
        if self.first_error.error().is_none() {
            self.first_error.record_error(error.clone());
        }
    }
}

impl<'a, 'tcx: 'a> Analysis<'tcx> for PcgEngine<'a, 'tcx> {
    type Domain = PcgDomain<'a, 'tcx>;
    const NAME: &'static str = "pcg";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        PcgDomain::bottom()
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        if state.is_bottom() {
            *state = PcgDomain::Analysis(DataflowState::Transfer(DomainDataWithCtxt::new(
                PcgDomainData::start_block(self.analysis_ctxt(START_BLOCK)),
                self.analysis_ctxt(START_BLOCK),
            )));
        } else {
            pcg_validity_assert!(state.is_results(), "unexpected state: {:?}", state);
        }
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

    type Direction = Forward;
}
