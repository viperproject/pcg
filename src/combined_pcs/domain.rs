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

use crate::{rustc_interface::{
    dataflow::{fmt::DebugWithContext, JoinSemiLattice}, middle::mir::BasicBlock,
}, RECORD_PCG};

use super::{PCGContext, PCGEngine};
use crate::borrows::domain::BorrowsDomain;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::{
    borrows::unblock_graph::{UnblockGraph, UnblockType},
    combined_pcs::PCGNode,
    free_pcs::{CapabilityLocal, FreePlaceCapabilitySummary},
    visualization::generate_dot_graph,
};

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
    pub(crate) fn to_filename_str_part(&self) -> String {
        match self {
            DataflowStmtPhase::Join(block) => format!("join_{:?}", block),
            _ => format!("{:?}", self),
        }
    }
}

#[derive(Clone)]
pub struct PlaceCapabilitySummary<'a, 'tcx> {
    cgx: Rc<PCGContext<'a, 'tcx>>,
    pub(crate) block: Option<BasicBlock>,

    pub(crate) pcg: PCG<'a, 'tcx>,
    dot_graphs: Option<Rc<RefCell<DotGraphs>>>,

    dot_output_dir: Option<String>,
}

/// Outermost Vec can be considered a map StatementIndex -> Vec<BTreeMap<DataflowStmtPhase, String>>
/// The inner Vec has one entry per iteration.
/// The BTreeMap maps each phase to a filename for the dot graph
#[derive(Clone)]
pub struct DotGraphs(Vec<Vec<BTreeMap<DataflowStmtPhase, String>>>);

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
                    .into_iter()
                    .map(|map| {
                        map.into_iter()
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PCGError {
    Unsupported(PCGUnsupportedError),
    Internal(PCGInternalError),
}

impl PCGError {
    pub(crate) fn unsupported(msg: String) -> Self {
        Self::Unsupported(PCGUnsupportedError::Other(msg))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PCGInternalError(String);

impl PCGInternalError {
    pub(crate) fn new(msg: String) -> Self {
        Self(msg)
    }
}

impl From<PCGInternalError> for PCGError {
    fn from(e: PCGInternalError) -> Self {
        PCGError::Internal(e)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PCGUnsupportedError {
    AssignBorrowToNonReferenceType,
    ClosuresCapturingBorrows,
    CastToRef,
    UnsafePtrCast,
    DerefUnsafePtr,
    InlineAssembly,
    TwoPhaseBorrow,
    ExpansionOfAliasType,
    Other(String),
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct PCG<'a, 'tcx> {
    pub(crate) owned: FreePlaceCapabilitySummary<'a, 'tcx>,
    pub(crate) borrow: BorrowsDomain<'a, 'tcx>,
}

impl<'a, 'tcx> PCG<'a, 'tcx> {
    pub(crate) fn initialize_as_start_block(&mut self) {
        self.owned.initialize_as_start_block();
        self.borrow.initialize_as_start_block();
    }
}

impl<'a, 'tcx> PlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) fn has_error(&self) -> bool {
        self.borrow_pcg().has_error() || self.owned_pcg().error.is_some()
    }

    pub(crate) fn pcg_mut(&mut self) -> &mut PCG<'a, 'tcx> {
        &mut self.pcg
    }

    pub(crate) fn borrow_pcg_mut(&mut self) -> &mut BorrowsDomain<'a, 'tcx> {
        &mut self.pcg.borrow
    }

    pub(crate) fn owned_pcg_mut(&mut self) -> &mut FreePlaceCapabilitySummary<'a, 'tcx> {
        &mut self.pcg.owned
    }

    pub(crate) fn owned_pcg(&self) -> &FreePlaceCapabilitySummary<'a, 'tcx> {
        &self.pcg.owned
    }

    pub(crate) fn borrow_pcg(&self) -> &BorrowsDomain<'a, 'tcx> {
        &self.pcg.borrow
    }

    pub(crate) fn is_initialized(&self) -> bool {
        self.block.is_some()
    }

    pub(crate) fn set_block(&mut self, block: BasicBlock) {
        self.block = Some(block);
        self.pcg.borrow.set_block(block);
    }

    pub fn set_dot_graphs(&mut self, dot_graphs: Rc<RefCell<DotGraphs>>) {
        self.dot_graphs = Some(dot_graphs);
    }

    pub(crate) fn block(&self) -> BasicBlock {
        self.block.unwrap()
    }

    pub fn dot_graphs(&self) -> Rc<RefCell<DotGraphs>> {
        self.dot_graphs.clone().unwrap()
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
            self.dot_graphs()
                .borrow()
                .relative_filename(phase, self.block(), statement_index)
        )
    }

    pub(crate) fn generate_dot_graph(&mut self, phase: DataflowStmtPhase, statement_index: usize) {
        if !*RECORD_PCG.lock().unwrap() {
            return;
        }
        if self.block().as_usize() == 0 {
            assert!(!matches!(phase, DataflowStmtPhase::Join(_)));
        }
        if let Some(output_dir) = &self.dot_output_dir {
            if phase == DataflowStmtPhase::Initial {
                self.dot_graphs()
                    .borrow_mut()
                    .register_new_iteration(statement_index);
            }
            let relative_filename =
                self.dot_graphs()
                    .borrow()
                    .relative_filename(phase, self.block(), statement_index);
            let filename = self.dot_filename_for(&output_dir, phase, statement_index);
            if !self
                .dot_graphs()
                .borrow_mut()
                .insert(statement_index, phase, relative_filename)
            {
                panic!(
                    "Dot graph for entry ({}, {:?}) already exists",
                    statement_index, phase
                )
            }

            let pcg = &self.pcg;

            let (fpcs, borrows) = match phase {
                DataflowStmtPhase::EvalStmt(phase) => (
                    &pcg.owned.data.states[phase],
                    &pcg.borrow.data.states[phase],
                ),
                _ => (&pcg.owned.data.entry_state, &pcg.borrow.data.entry_state),
            };

            generate_dot_graph(self.cgx.rp, fpcs, borrows, &filename).unwrap();
        }
    }

    pub(crate) fn new(
        cgx: Rc<PCGContext<'a, 'tcx>>,
        block: Option<BasicBlock>,
        dot_output_dir: Option<String>,
        dot_graphs: Option<Rc<RefCell<DotGraphs>>>,
    ) -> Self {
        let fpcs = FreePlaceCapabilitySummary::new(cgx.rp);
        let borrows = BorrowsDomain::new(
            cgx.rp,
            cgx.mir.region_inference_context.clone(),
            cgx.mir.borrow_set.clone(),
            block,
        );
        let pcg = PCG {
            owned: fpcs,
            borrow: borrows,
        };
        Self {
            cgx,
            block,
            pcg,
            dot_graphs,
            dot_output_dir,
        }
    }
}

impl Eq for PlaceCapabilitySummary<'_, '_> {}
impl PartialEq for PlaceCapabilitySummary<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.pcg == other.pcg
    }
}
impl Debug for PlaceCapabilitySummary<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}\n{:?}", self.owned_pcg(), self.borrow_pcg())
    }
}

impl JoinSemiLattice for PlaceCapabilitySummary<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        if other.has_error() && !self.has_error() {
            self.pcg = other.pcg.clone();
            return true;
        } else if self.has_error() {
            return false;
        }
        // For performance reasons we don't check validity here.
        // if validity_checks_enabled() {
        //     if !other.is_valid() {
        //         eprintln!(
        //             "Block {:?} is invalid. Body source: {:?}, span: {:?}",
        //             other.block(),
        //             self.cgx.mir.body.source,
        //             self.cgx.mir.body.span
        //         );
        //     }
        //     debug_assert!(other.is_valid(), "Block {:?} is invalid!", other.block());
        // }
        assert!(self.is_initialized() && other.is_initialized());
        if self.block().as_usize() == 0 {
            panic!("{:?}", other.block());
        }
        let fpcs = self.owned_pcg_mut().join(&other.owned_pcg());
        if self.owned_pcg().has_internal_error() {
            panic!(
                "Error joining (self:{:?}, other:{:?}): {:?}",
                self.block(),
                other.block(),
                self.owned_pcg().error.as_ref().unwrap()
            );
        }
        let borrows = self.borrow_pcg_mut().join(&other.borrow_pcg());
        let mut g = UnblockGraph::new();
        for root in self.borrow_pcg().data.entry_state.roots(self.cgx.rp) {
            if let PCGNode::Place(MaybeRemotePlace::Local(MaybeOldPlace::Current { place: root })) =
                root
            {
                match &self.owned_pcg().data.entry_state[root.local] {
                    CapabilityLocal::Unallocated => {
                        g.unblock_node(
                            root.into(),
                            &self.borrow_pcg().data.entry_state,
                            self.cgx.rp,
                            UnblockType::ForRead,
                        );
                    }
                    CapabilityLocal::Allocated(projs) => {
                        if !(*projs).contains_key(&root) {
                            g.unblock_node(
                                root.into(),
                                &self.borrow_pcg().data.entry_state,
                                self.cgx.rp,
                                UnblockType::ForExclusive,
                            );
                        }
                    }
                }
            }
        }
        self.dot_graphs().borrow_mut().register_new_iteration(0);
        self.generate_dot_graph(DataflowStmtPhase::Join(other.block()), 0);
        fpcs || borrows
    }
}

impl<'a, 'tcx> DebugWithContext<PCGEngine<'a, 'tcx>> for PlaceCapabilitySummary<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &PCGEngine<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        self.pcg.owned.fmt_diff_with(&old.pcg.owned, &ctxt.fpcs, f)
    }
}
