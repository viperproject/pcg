// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use itertools::Itertools;
use std::{
    cell::RefCell,
    collections::BTreeMap,
    fmt::{Debug, Formatter, Result},
    rc::Rc,
};

use crate::{
    borrow_pcg::coupling_graph_constructor::BorrowCheckerInterface,
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::mir::BasicBlock,
        mir_dataflow::{fmt::DebugWithContext, JoinSemiLattice},
    },
    utils::PlaceRepacker,
    PCGAnalysis, RECORD_PCG,
};

use super::PCGEngine;
use crate::borrow_pcg::domain::BorrowsDomain;
use crate::{free_pcs::FreePlaceCapabilitySummary, visualization::generate_dot_graph};

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
            DataflowStmtPhase::Join(block) => format!("join_{:?}", block),
            _ => format!("{:?}", self),
        }
    }
}

#[derive(Clone)]
pub(crate) struct PCGDebugData {
    pub(crate) dot_output_dir: String,
    pub(crate) dot_graphs: Rc<RefCell<DotGraphs>>,
}

#[derive(Clone, Eq)]
pub struct Pcg<'a, 'tcx> {
    pub(crate) owned: FreePlaceCapabilitySummary<'a, 'tcx>,
    pub(crate) borrow: BorrowsDomain<'a, 'tcx>,
}

impl PartialEq for Pcg<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.owned == other.owned && self.borrow == other.borrow
    }
}

impl Pcg<'_, '_> {
    pub(crate) fn initialize_as_start_block(&mut self) {
        self.owned.initialize_as_start_block();
        self.borrow.initialize_as_start_block();
    }
}

#[derive(Clone)]
pub struct PlaceCapabilitySummary<'a, 'tcx> {
    repacker: PlaceRepacker<'a, 'tcx>,
    pub(crate) block: Option<BasicBlock>,
    pub(crate) pcg: std::result::Result<Pcg<'a, 'tcx>, PcgError>,
    pub(crate) debug_data: Option<PCGDebugData>,
    pub(crate) join_history: FxHashSet<BasicBlock>,
    pub(crate) reachable: bool,
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
                            .map(|(phase, filename)| (format!("{:?}", phase), filename))
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

    pub(crate) fn add_context(&mut self, context: String) {
        self.context.push(context);
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
    ClosureCall,
}

impl<'a, 'tcx> PlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) fn has_error(&self) -> bool {
        self.pcg.is_err()
    }

    pub(crate) fn error(&self) -> Option<&PcgError> {
        self.pcg.as_ref().err()
    }

    pub(crate) fn record_error(&mut self, error: PcgError) {
        self.pcg = Err(error);
    }

    pub(crate) fn pcg(&self) -> &Pcg<'a, 'tcx> {
        match &self.pcg {
            Ok(pcg) => pcg,
            Err(e) => panic!("PCG error: {:?}", e),
        }
    }

    pub(crate) fn pcg_mut(&mut self) -> &mut Pcg<'a, 'tcx> {
        match &mut self.pcg {
            Ok(pcg) => pcg,
            Err(e) => panic!("PCG error: {:?}", e),
        }
    }

    pub(crate) fn borrow_pcg_mut(&mut self) -> &mut BorrowsDomain<'a, 'tcx> {
        &mut self.pcg_mut().borrow
    }

    pub(crate) fn owned_pcg_mut(&mut self) -> &mut FreePlaceCapabilitySummary<'a, 'tcx> {
        &mut self.pcg_mut().owned
    }

    pub(crate) fn owned_pcg(&self) -> &FreePlaceCapabilitySummary<'a, 'tcx> {
        &self.pcg().owned
    }

    pub(crate) fn borrow_pcg(&self) -> &BorrowsDomain<'a, 'tcx> {
        &self.pcg().borrow
    }

    pub(crate) fn is_initialized(&self) -> bool {
        self.block.is_some()
    }

    pub(crate) fn set_block(&mut self, block: BasicBlock) {
        self.block = Some(block);
        self.pcg_mut().borrow.set_block(block);
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

    pub(crate) fn generate_dot_graph(&mut self, phase: DataflowStmtPhase, statement_index: usize) {
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
                panic!(
                    "Dot graph for entry ({}, {:?}) already exists",
                    statement_index, phase
                )
            }

            let pcg = &self.pcg();

            let (fpcs, borrows) = match phase {
                DataflowStmtPhase::EvalStmt(phase) => (
                    &pcg.owned.data.states[phase],
                    &pcg.borrow.data.states[phase],
                ),
                _ => (&pcg.owned.data.entry_state, &pcg.borrow.data.entry_state),
            };

            generate_dot_graph(
                self.repacker,
                fpcs.as_ref().as_ref().unwrap(),
                borrows,
                &filename,
            )
            .unwrap();
        }
    }

    pub(crate) fn new(
        repacker: PlaceRepacker<'a, 'tcx>,
        bc: Rc<dyn BorrowCheckerInterface<'a, 'tcx> + 'a>,
        block: Option<BasicBlock>,
        debug_data: Option<PCGDebugData>,
    ) -> Self {
        let fpcs = FreePlaceCapabilitySummary::new(repacker);
        let borrows = BorrowsDomain::new(repacker, bc, block);
        let pcg = Pcg {
            owned: fpcs,
            borrow: borrows,
        };
        Self {
            repacker,
            block,
            pcg: Ok(pcg),
            debug_data,
            join_history: FxHashSet::default(),
            reachable: false,
        }
    }
}

impl Debug for PlaceCapabilitySummary<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}\n{:?}", self.owned_pcg(), self.borrow_pcg())
    }
}

impl Eq for PlaceCapabilitySummary<'_, '_> {}

impl PartialEq for PlaceCapabilitySummary<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.pcg == other.pcg
    }
}

impl JoinSemiLattice for PlaceCapabilitySummary<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        if !self.reachable && !other.reachable {
            return false;
        }
        if other.has_error() && !self.has_error() {
            self.pcg = other.pcg.clone();
            return true;
        } else if self.has_error() {
            return false;
        }

        let self_block = self.block();
        let other_block = other.block();

        if self.repacker.is_back_edge(other_block, self_block)
            && self.join_history.contains(&other_block)
        {
            // We've already joined this block, we can exit early
            return false;
        } else {
            self.join_history.insert(other_block);
        }
        assert!(self.is_initialized() && other.is_initialized());
        let fpcs = match self
            .owned_pcg_mut()
            .join(other.owned_pcg(), self_block, other_block)
        {
            Ok(changed) => changed,
            Err(e) => {
                self.record_error(e);
                return false;
            }
        };
        let borrows = self.borrow_pcg_mut().join(other.borrow_pcg());
        if let Some(debug_data) = &self.debug_data {
            debug_data.dot_graphs.borrow_mut().register_new_iteration(0);
            self.generate_dot_graph(DataflowStmtPhase::Join(other.block()), 0);
        }
        fpcs || borrows
    }
}

impl<'a, 'tcx> DebugWithContext<PCGAnalysis<PCGEngine<'a, 'tcx>>>
    for PlaceCapabilitySummary<'a, 'tcx>
{
    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &PCGAnalysis<PCGEngine<'a, 'tcx>>,
        f: &mut Formatter<'_>,
    ) -> Result {
        self.pcg()
            .owned
            .fmt_diff_with(&old.pcg().owned, &ctxt.0.fpcs, f)
    }
}
