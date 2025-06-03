// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use itertools::Itertools;
use std::{
    alloc::Allocator,
    cell::RefCell,
    collections::BTreeMap,
    fmt::{Debug, Formatter, Result},
    rc::Rc,
};

use crate::{
    action::PcgActions,
    borrow_pcg::state::BorrowsState,
    borrows_imgcat_debug,
    pcg::triple::Triple,
    rustc_interface::{
        middle::mir::{self, BasicBlock},
        mir_dataflow::{fmt::DebugWithContext, JoinSemiLattice},
    },
    utils::{
        arena::ArenaRef,
        domain_data::{DomainData, DomainDataIndex},
        eval_stmt_data::EvalStmtData,
        incoming_states::IncomingStates,
        validity::HasValidityCheck,
        CompilerCtxt,
    },
    validity_checks_enabled, validity_checks_warn_only,
    visualization::{dot_graph::DotGraph, generate_pcg_dot_graph},
    AnalysisEngine, DebugLines, RECORD_PCG,
};

use super::{place_capabilities::PlaceCapabilities, PcgEngine};
use crate::{free_pcs::FreePlaceCapabilitySummary, visualization::write_pcg_dot_graph_to_file};

#[derive(Copy, Clone)]
pub struct DataflowIterationDebugInfo {
    pub join_with: BasicBlock,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Ord, PartialOrd)]
pub enum EvalStmtPhase {
    PreOperands,
    PostOperands,
    PreMain,
    PostMain,
}

impl EvalStmtPhase {
    pub fn phases() -> [EvalStmtPhase; 4] {
        [
            EvalStmtPhase::PreOperands,
            EvalStmtPhase::PostOperands,
            EvalStmtPhase::PreMain,
            EvalStmtPhase::PostMain,
        ]
    }

    pub(crate) fn next(&self) -> Option<EvalStmtPhase> {
        match self {
            EvalStmtPhase::PreOperands => Some(EvalStmtPhase::PostOperands),
            EvalStmtPhase::PostOperands => Some(EvalStmtPhase::PreMain),
            EvalStmtPhase::PreMain => Some(EvalStmtPhase::PostMain),
            EvalStmtPhase::PostMain => None,
        }
    }
}

impl std::fmt::Display for EvalStmtPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalStmtPhase::PreOperands => write!(f, "pre_operands"),
            EvalStmtPhase::PostOperands => write!(f, "post_operands"),
            EvalStmtPhase::PreMain => write!(f, "pre_main"),
            EvalStmtPhase::PostMain => write!(f, "post_main"),
        }
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Ord, PartialOrd)]
pub enum DataflowStmtPhase {
    Initial,
    EvalStmt(EvalStmtPhase),
    Join(BasicBlock),
}

impl From<EvalStmtPhase> for DataflowStmtPhase {
    fn from(phase: EvalStmtPhase) -> Self {
        DataflowStmtPhase::EvalStmt(phase)
    }
}

impl DataflowStmtPhase {
    pub(crate) fn to_filename_str_part(self) -> String {
        match self {
            DataflowStmtPhase::Join(block) => format!("join_{block:?}"),
            _ => format!("{self:?}"),
        }
    }
}

#[derive(Clone)]
pub(crate) struct PCGDebugData {
    pub(crate) dot_output_dir: String,
    pub(crate) dot_graphs: Rc<RefCell<DotGraphs>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Pcg<'tcx> {
    pub(crate) owned: FreePlaceCapabilitySummary<'tcx>,
    pub(crate) borrow: BorrowsState<'tcx>,
    pub(crate) capabilities: PlaceCapabilities<'tcx>,
}

impl<'tcx> Pcg<'tcx> {
    pub(crate) fn assert_validity_at_location(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
        location: mir::Location,
    ) {
        if validity_checks_enabled()
            && let Err(err) = self.check_validity(ctxt)
        {
            if borrows_imgcat_debug() {
                self.render_debug_graph(ctxt, location, "Validity check failed");
            }
            if validity_checks_warn_only() {
                tracing::error!("Validity check failed: {}", err.to_string());
            } else {
                panic!("Validity check failed: {}", err.to_string());
            }
        }
    }
}

impl<'tcx> HasValidityCheck<'tcx> for Pcg<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> std::result::Result<(), String> {
        self.borrow.check_validity(ctxt)?;
        // TODO
        if !self.is_acyclic(ctxt) {
            return Err("PCG is not acyclic".to_string());
        }
        Ok(())
    }
}

impl<'mir, 'tcx: 'mir> Pcg<'tcx> {
    pub(crate) fn is_acyclic(&self, ctxt: CompilerCtxt<'mir, 'tcx>) -> bool {
        self.borrow.graph().frozen_graph().is_acyclic(ctxt)
    }

    pub(crate) fn render_debug_graph(
        &self,
        ctxt: CompilerCtxt<'mir, 'tcx>,
        location: mir::Location,
        comment: &str,
    ) {
        if borrows_imgcat_debug() {
            let dot_graph = generate_pcg_dot_graph(self, ctxt, location).unwrap();
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }

    pub fn capabilities(&self) -> &PlaceCapabilities<'tcx> {
        &self.capabilities
    }

    pub fn owned_pcg(&self) -> &FreePlaceCapabilitySummary<'tcx> {
        &self.owned
    }

    pub fn borrow_pcg(&self) -> &BorrowsState<'tcx> {
        &self.borrow
    }

    pub(crate) fn owned_ensures(&mut self, t: Triple<'tcx>) {
        self.owned.locals_mut().ensures(t, &mut self.capabilities);
    }

    #[tracing::instrument(skip(self, other, ctxt))]
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> std::result::Result<bool, PcgError> {
        let mut res = self.owned.join(
            &other.owned,
            &mut self.capabilities,
            &other.capabilities,
            ctxt,
        )?;
        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let mut other = other.clone();
        other.borrow.add_cfg_edge(other_block, self_block, ctxt);
        res |= self
            .borrow
            .join(&other.borrow, self_block, other_block, ctxt);
        res |= self.capabilities.join(&other.capabilities);
        Ok(res)
    }

    pub(crate) fn debug_lines(&self, repacker: CompilerCtxt<'mir, 'tcx>) -> Vec<String> {
        let mut result = self.borrow.debug_lines(repacker);
        result.sort();
        let mut capabilities = self.capabilities.debug_lines(repacker);
        capabilities.sort();
        result.extend(capabilities);
        result
    }
    pub(crate) fn initialize_as_start_block(&mut self, repacker: CompilerCtxt<'_, 'tcx>) {
        self.owned
            .initialize_as_start_block(&mut self.capabilities, repacker);
        self.borrow
            .initialize_as_start_block(&mut self.capabilities, repacker);
    }
}

#[derive(Clone, Eq, Debug)]
pub struct PcgDomainData<'tcx, A: Allocator> {
    pub(crate) pcg: DomainData<ArenaRef<Pcg<'tcx>, A>>,
    pub(crate) actions: EvalStmtData<PcgActions<'tcx>>,
}

impl<'tcx, A: Allocator> PartialEq for PcgDomainData<'tcx, A> {
    fn eq(&self, other: &Self) -> bool {
        self.pcg == other.pcg
    }
}

impl<'tcx, A: Allocator + Clone> PcgDomainData<'tcx, A> {
    pub(crate) fn new(arena: A) -> Self {
        let pcg = ArenaRef::new_in(Pcg::default(), arena);
        Self {
            pcg: DomainData::new(pcg),
            actions: EvalStmtData::default(),
        }
    }
}

#[derive(Clone)]
pub struct PcgDomain<'a, 'tcx, A: Allocator> {
    ctxt: CompilerCtxt<'a, 'tcx>,
    pub(crate) block: Option<BasicBlock>,
    pub(crate) data: std::result::Result<PcgDomainData<'tcx, A>, PcgError>,
    pub(crate) debug_data: Option<PCGDebugData>,
    pub(crate) reachable: bool,
}

impl<'a, 'tcx, A: Allocator + Debug> Debug for PcgDomain<'a, 'tcx, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}", self.data)
    }
}

/// Outermost Vec can be considered a map StatementIndex -> Vec<BTreeMap<DataflowStmtPhase, String>>
/// The inner Vec has one entry per iteration.
/// The BTreeMap maps each phase to a filename for the dot graph
#[derive(Clone)]
pub struct DotGraphs(Vec<Vec<BTreeMap<DataflowStmtPhase, String>>>);

impl Default for DotGraphs {
    fn default() -> Self {
        Self::new()
    }
}

impl DotGraphs {
    pub fn new() -> Self {
        Self(vec![])
    }

    fn relative_filename(
        &self,
        phase: DataflowStmtPhase,
        block: BasicBlock,
        statement_index: usize,
    ) -> String {
        let iteration = self.num_iterations(statement_index);
        format!(
            "{:?}_stmt_{}_iteration_{}_{}.dot",
            block,
            statement_index,
            iteration,
            phase.to_filename_str_part()
        )
    }

    pub fn register_new_iteration(&mut self, statement_index: usize) {
        if self.0.len() <= statement_index {
            self.0.resize_with(statement_index + 1, Vec::new);
        }
        self.0[statement_index].push(BTreeMap::new());
    }

    pub fn num_iterations(&self, statement_index: usize) -> usize {
        self.0[statement_index].len()
    }

    pub(crate) fn insert(
        &mut self,
        statement_index: usize,
        phase: DataflowStmtPhase,
        filename: String,
    ) -> bool {
        let top = self.0[statement_index].last_mut().unwrap();
        top.insert(phase, filename).is_none()
    }

    pub(crate) fn write_json_file(&self, filename: &str) {
        let iterations_json = self
            .0
            .iter()
            .map(|iterations| {
                iterations
                    .iter()
                    .map(|map| {
                        map.iter()
                            .sorted_by_key(|x| x.0)
                            .map(|(phase, filename)| (format!("{phase:?}"), filename))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        std::fs::write(
            filename,
            serde_json::to_string_pretty(&iterations_json).unwrap(),
        )
        .unwrap();
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct ErrorState {
    error: Option<PcgError>,
}

impl ErrorState {
    pub(crate) fn error(&self) -> Option<&PcgError> {
        self.error.as_ref()
    }

    pub(crate) fn record_error(&mut self, error: PcgError) {
        tracing::error!("PCG Error: {:?}", error);
        self.error = Some(error);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PcgError {
    pub(crate) kind: PCGErrorKind,
    pub(crate) context: Vec<String>,
}

// Deprecated: use PcgError instead
pub type PCGError = PcgError;

impl From<PCGUnsupportedError> for PcgError {
    fn from(e: PCGUnsupportedError) -> Self {
        Self::new(PCGErrorKind::Unsupported(e), vec![])
    }
}

impl PcgError {
    pub(crate) fn new(kind: PCGErrorKind, context: Vec<String>) -> Self {
        Self { kind, context }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PCGErrorKind {
    Unsupported(PCGUnsupportedError),
    Internal(PCGInternalError),
}

impl PcgError {
    pub(crate) fn internal(msg: String) -> Self {
        Self {
            kind: PCGErrorKind::Internal(PCGInternalError::new(msg)),
            context: vec![],
        }
    }

    pub(crate) fn unsupported(err: PCGUnsupportedError) -> Self {
        Self {
            kind: PCGErrorKind::Unsupported(err),
            context: vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PCGInternalError(String);

impl PCGInternalError {
    pub(crate) fn new(msg: String) -> Self {
        Self(msg)
    }
}

impl From<PCGInternalError> for PcgError {
    fn from(e: PCGInternalError) -> Self {
        PcgError::new(PCGErrorKind::Internal(e), vec![])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PCGUnsupportedError {
    AssignBorrowToNonReferenceType,
    DerefUnsafePtr,
    ExpansionOfAliasType,
    IndexingNonIndexableType,
    InlineAssembly,
}

impl<'a, 'tcx, A: Allocator + Clone> PcgDomain<'a, 'tcx, A> {
    pub(crate) fn has_error(&self) -> bool {
        self.data.is_err()
    }

    pub(crate) fn error(&self) -> Option<&PcgError> {
        self.data.as_ref().err()
    }

    pub(crate) fn record_error(&mut self, error: PcgError) {
        self.data = Err(error);
    }

    pub(crate) fn data(&self) -> std::result::Result<&PcgDomainData<'tcx, A>, PcgError> {
        self.data.as_ref().map_err(|e| e.clone())
    }

    pub(crate) fn pcg_mut(&mut self, phase: DomainDataIndex) -> &mut Pcg<'tcx> {
        match &mut self.data {
            Ok(data) => ArenaRef::make_mut(&mut data.pcg[phase]),
            Err(e) => panic!("PCG error: {e:?}"),
        }
    }
    pub fn pcg(&self, phase: impl Into<DomainDataIndex>) -> &Pcg<'tcx> {
        match &self.data {
            Ok(data) => &data.pcg[phase.into()],
            Err(e) => panic!("PCG error: {e:?}"),
        }
    }

    pub(crate) fn is_initialized(&self) -> bool {
        self.block.is_some()
    }

    pub(crate) fn set_block(&mut self, block: BasicBlock) {
        self.block = Some(block);
    }

    pub fn set_debug_data(&mut self, output_dir: String, dot_graphs: Rc<RefCell<DotGraphs>>) {
        self.debug_data = Some(PCGDebugData {
            dot_output_dir: output_dir,
            dot_graphs,
        });
    }

    pub(crate) fn block(&self) -> BasicBlock {
        self.block.unwrap()
    }

    pub fn dot_graphs(&self) -> Option<Rc<RefCell<DotGraphs>>> {
        self.debug_data.as_ref().map(|data| data.dot_graphs.clone())
    }

    fn dot_filename_for(
        &self,
        output_dir: &str,
        phase: DataflowStmtPhase,
        statement_index: usize,
    ) -> String {
        format!(
            "{}/{}",
            output_dir,
            self.dot_graphs().unwrap().borrow().relative_filename(
                phase,
                self.block(),
                statement_index
            )
        )
    }

    pub(crate) fn generate_dot_graph(&self, phase: DataflowStmtPhase, statement_index: usize) {
        if !*RECORD_PCG.lock().unwrap() {
            return;
        }
        if self.block().as_usize() == 0 {
            assert!(!matches!(phase, DataflowStmtPhase::Join(_)));
        }
        if let Some(debug_data) = &self.debug_data {
            if phase == DataflowStmtPhase::Initial {
                debug_data
                    .dot_graphs
                    .borrow_mut()
                    .register_new_iteration(statement_index);
            }
            let relative_filename = debug_data.dot_graphs.borrow().relative_filename(
                phase,
                self.block(),
                statement_index,
            );
            let filename =
                self.dot_filename_for(&debug_data.dot_output_dir, phase, statement_index);
            if !debug_data
                .dot_graphs
                .borrow_mut()
                .insert(statement_index, phase, relative_filename)
            {
                panic!("Dot graph for entry ({statement_index}, {phase:?}) already exists")
            }

            let pcg: &Pcg<'tcx> = match phase {
                DataflowStmtPhase::EvalStmt(phase) => self.pcg(DomainDataIndex::Eval(phase)),
                _ => self.pcg(DomainDataIndex::Initial),
            };

            write_pcg_dot_graph_to_file(
                pcg,
                self.ctxt,
                mir::Location {
                    block: self.block(),
                    statement_index,
                },
                &filename,
            )
            .unwrap();
        }
    }

    pub(crate) fn new(
        repacker: CompilerCtxt<'a, 'tcx>,
        block: Option<BasicBlock>,
        debug_data: Option<PCGDebugData>,
        arena: A,
    ) -> Self {
        Self {
            ctxt: repacker,
            block,
            data: Ok(PcgDomainData::new(arena)),
            debug_data,
            reachable: false,
        }
    }
}

impl<'a, 'tcx, A: Allocator + Clone> Eq for PcgDomain<'a, 'tcx, A> {}

impl<'a, 'tcx, A: Allocator + Clone> PartialEq for PcgDomain<'a, 'tcx, A> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<'a, 'tcx, A: Allocator + Clone> JoinSemiLattice for PcgDomain<'a, 'tcx, A> {
    fn join(&mut self, other: &Self) -> bool {
        if !self.reachable && !other.reachable {
            return false;
        }
        if other.has_error() && !self.has_error() {
            self.data = other.data.clone();
            return true;
        }

        let self_block = self.block();
        let other_block = other.block();

        let data = match &mut self.data {
            Ok(data) => data,
            Err(_) => return false,
        };

        let seen = data.pcg.incoming_states.contains(other_block);

        if seen && self.ctxt.is_back_edge(other_block, self_block) {
            // It's a loop, but we've already joined it
            return false;
        }

        let first_join = data.pcg.incoming_states.is_empty();

        if first_join || seen {
            // Either this is the first time we're joining the block (and we
            // should inherit the existing state) or we're seeing the same block
            // for the first time again.
            // In either case, we should inherit the state from the other block.
            data.pcg.incoming_states = IncomingStates::singleton(other_block);

            let other_state = &other.data.as_ref().unwrap().pcg.states[EvalStmtPhase::PostMain];
            data.pcg.entry_state = other_state.clone();
            let entry_state_mut = ArenaRef::make_mut(&mut data.pcg.entry_state);
            entry_state_mut
                .borrow
                .add_cfg_edge(other_block, self_block, self.ctxt);
            return true;
        } else {
            data.pcg.incoming_states.insert(other_block);
        }

        assert!(self.is_initialized() && other.is_initialized());
        let pcg =
            ArenaRef::make_mut(&mut self.data.as_mut().unwrap().pcg[DomainDataIndex::Initial]);
        let result = match pcg.join(
            other.pcg(DomainDataIndex::Eval(EvalStmtPhase::PostMain)),
            self_block,
            other_block,
            self.ctxt,
        ) {
            Ok(changed) => changed,
            Err(e) => {
                self.record_error(e);
                false
            }
        };
        if let Some(debug_data) = &self.debug_data {
            debug_data.dot_graphs.borrow_mut().register_new_iteration(0);
            self.generate_dot_graph(DataflowStmtPhase::Join(other.block()), 0);
        }
        result
    }
}

impl<'a, 'tcx, A: Allocator + Clone + Debug>
    DebugWithContext<AnalysisEngine<PcgEngine<'a, 'tcx, A>>> for PcgDomain<'a, 'tcx, A>
{
    fn fmt_diff_with(
        &self,
        _old: &Self,
        _ctxt: &AnalysisEngine<PcgEngine<'a, 'tcx, A>>,
        _f: &mut Formatter<'_>,
    ) -> Result {
        Ok(())
    }
}
