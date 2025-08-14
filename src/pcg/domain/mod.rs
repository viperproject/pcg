// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cell::RefCell,
    fmt::{Debug, Formatter},
    marker::PhantomData,
    rc::Rc,
};

use derive_more::{From, TryInto};
use serde::{Serialize, Serializer};

use crate::{
    AnalysisEngine,
    action::PcgActions,
    borrow_checker::BorrowCheckerInterface,
    r#loop::{LoopAnalysis, LoopPlaceUsageAnalysis, PlaceUsages},
    pcg::{
        CapabilityOps, PcgArena, SymbolicCapability,
        ctxt::AnalysisCtxt,
        dot_graphs::{PcgDotGraphsForBlock, ToGraph, generate_dot_graph},
        place_capabilities::SymbolicPlaceCapabilities,
    },
    pcg_validity_assert,
    rustc_interface::{
        middle::mir::{self, BasicBlock},
        mir_dataflow::{JoinSemiLattice, fmt::DebugWithContext, move_paths::MoveData},
    },
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, PANIC_ON_ERROR, Place,
        arena::PcgArenaRef,
        data_structures::HashSet,
        domain_data::{DomainData, DomainDataIndex},
        eval_stmt_data::EvalStmtData,
        incoming_states::IncomingStates,
        initialized::DefinitelyInitialized,
        liveness::PlaceLiveness,
    },
};

mod dataflow_stmt_phase;
mod eval_stmt_phase;
mod pcg;

pub use dataflow_stmt_phase::*;
pub use eval_stmt_phase::*;
pub use pcg::*;

use super::PcgEngine;
use crate::owned_pcg::OwnedPcg;

#[derive(Copy, Clone)]
pub struct DataflowIterationDebugInfo {
    pub join_with: BasicBlock,
}

#[derive(Clone, Debug)]
pub(crate) struct PcgDebugData {
    pub(crate) dot_output_dir: String,
    pub(crate) dot_graphs: Rc<RefCell<PcgDotGraphsForBlock>>,
}

#[derive(Clone, Eq, Debug)]
pub struct PcgDomainData<'a, 'tcx, Capabilities = SymbolicPlaceCapabilities<'a, 'tcx>> {
    pub(crate) pcg: DomainData<PcgArenaRef<'a, Pcg<'a, 'tcx, Capabilities>>>,
    pub(crate) actions: EvalStmtData<PcgActions<'tcx>>,
}

pub(crate) trait HasBlock {
    fn block(&self) -> mir::BasicBlock;
}

impl<'a, 'tcx> HasBlock for AnalysisCtxt<'a, 'tcx> {
    fn block(&self) -> mir::BasicBlock {
        self.block
    }
}

impl<'a, 'tcx> PcgDomainData<'a, 'tcx> {
    pub(crate) fn from_incoming(
        self_block: mir::BasicBlock,
        other: &DomainDataWithCtxt<'a, 'tcx, AnalysisCtxt<'a, 'tcx>>,
    ) -> Self {
        pcg_validity_assert!(self_block != other.ctxt.block);
        let mut entry_state = (*other.data.pcg.states.0.post_main).clone();
        entry_state
            .borrow
            .add_cfg_edge(other.ctxt.block, self_block, other.ctxt.ctxt);
        let domain_data = DomainData::new(Rc::new_in(entry_state, other.ctxt.arena));
        Self {
            pcg: domain_data,
            actions: EvalStmtData::default(),
        }
    }

    pub(crate) fn start_block(ctxt: AnalysisCtxt<'a, 'tcx>) -> Self {
        let pcg = Pcg::start_block(ctxt);
        Self {
            pcg: DomainData::new(Rc::new_in(pcg, ctxt.arena)),
            actions: EvalStmtData::default(),
        }
    }
}

impl<Capabilities: PartialEq> PartialEq for PcgDomainData<'_, '_, Capabilities> {
    fn eq(&self, other: &Self) -> bool {
        self.pcg == other.pcg
    }
}

impl<'a, 'tcx: 'a> PcgDomainData<'a, 'tcx> {
    pub(crate) fn pcg_mut(&mut self, phase: DomainDataIndex) -> &mut Pcg<'a, 'tcx> {
        PcgArenaRef::make_mut(&mut self.pcg[phase])
    }
}

#[derive(Clone)]
pub(crate) struct BodyAnalysis<'a, 'tcx> {
    pub(crate) definitely_initialized: DefinitelyInitialized<'a, 'tcx>,
    pub(crate) place_liveness: PlaceLiveness<'a, 'tcx>,
    pub(crate) loop_analysis: LoopPlaceUsageAnalysis<'tcx>,
}

impl<'a, 'tcx> BodyAnalysis<'a, 'tcx> {
    pub(crate) fn new(ctxt: CompilerCtxt<'a, 'tcx>, move_data: &'a MoveData<'tcx>) -> Self {
        let definitely_initialized = DefinitelyInitialized::new(ctxt.tcx(), ctxt.body(), move_data);
        let place_liveness = PlaceLiveness::new(ctxt);
        let loop_analysis = LoopAnalysis::find_loops(ctxt.body());
        let loop_place_analysis =
            LoopPlaceUsageAnalysis::new(ctxt.tcx(), ctxt.body(), &loop_analysis);
        Self {
            definitely_initialized,
            place_liveness,
            loop_analysis: loop_place_analysis,
        }
    }

    pub(crate) fn is_loop_head(&self, block: BasicBlock) -> bool {
        self.loop_analysis.is_loop_head(block)
    }

    pub(crate) fn get_places_used_in_loop(
        &self,
        loop_head: BasicBlock,
    ) -> Option<&PlaceUsages<'tcx>> {
        self.loop_analysis.get_used_places(loop_head)
    }

    pub(crate) fn is_live_and_initialized_at(
        &self,
        location: mir::Location,
        place: Place<'tcx>,
    ) -> bool {
        self.place_liveness.is_live(place, location)
            && self.is_definitely_initialized_at(location, place)
    }

    pub(crate) fn is_definitely_initialized_at(
        &self,
        location: mir::Location,
        place: Place<'tcx>,
    ) -> bool {
        self.definitely_initialized
            .is_definitely_initialized(location, place)
    }
}

impl std::fmt::Debug for PcgDomain<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PcgDomain::Error(pcg_error) => write!(f, "Error({:?})", pcg_error),
            PcgDomain::Analysis(dataflow_state) => {
                write!(f, "Analysis({:?})", dataflow_state)
            }
            PcgDomain::Results(dataflow_state) => {
                write!(f, "Results({:?})", dataflow_state)
            }
            PcgDomain::Bottom => write!(f, "Bottom"),
        }
    }
}

#[derive(Clone)]
pub enum DataflowState<'a, 'tcx, T> {
    Pending(Vec<DomainDataWithCtxt<'a, 'tcx, T>>),
    Transfer(DomainDataWithCtxt<'a, 'tcx, T>),
}

impl<'a, 'tcx, T> DataflowState<'a, 'tcx, T> {
    pub(crate) fn expect_pending(&self) -> &Vec<DomainDataWithCtxt<'a, 'tcx, T>> {
        match self {
            DataflowState::Pending(pending) => pending,
            _ => panic!("Expected pending domain, got {:?}", self),
        }
    }

    pub(crate) fn expect_transfer(&self) -> &DomainDataWithCtxt<'a, 'tcx, T> {
        match self {
            DataflowState::Transfer(transfer) => transfer,
            _ => panic!("Expected transfer domain, got {:?}", self),
        }
    }

    pub(crate) fn expect_transfer_mut(&mut self) -> &mut DomainDataWithCtxt<'a, 'tcx, T> {
        match self {
            DataflowState::Transfer(transfer) => transfer,
            _ => panic!("Expected transfer domain, got {:?}", self),
        }
    }
}

impl<'a, 'tcx, T> PartialEq for DataflowState<'a, 'tcx, T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (DataflowState::Pending(d1), DataflowState::Pending(d2)) => d1 == d2,
            (DataflowState::Transfer(d1), DataflowState::Transfer(d2)) => d1 == d2,
            _ => false,
        }
    }
}

impl<'a, 'tcx, T> Eq for DataflowState<'a, 'tcx, T> {}

impl<'a, 'tcx, T> std::fmt::Debug for DataflowState<'a, 'tcx, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DataflowState::Pending(pending) => write!(f, "Pending"),
            DataflowState::Transfer(transfer) => write!(f, "Transfer"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct DomainDataWithCtxt<'a, 'tcx, T> {
    pub(crate) ctxt: T,
    pub(crate) data: PcgDomainData<'a, 'tcx>,
    pub(crate) debug_data: Option<PcgDebugData>,
}

impl<'a, 'tcx: 'a> HasPcgDomainData<'a, 'tcx> for PcgDomain<'a, 'tcx> {
    fn data(&self) -> &PcgDomainData<'a, 'tcx> {
        match self {
            PcgDomain::Analysis(dataflow_state) => &dataflow_state.expect_transfer().data,
            PcgDomain::Results(data) => &data.data,
            _ => panic!("Expected analysis or results domain, got {:?}", self),
        }
    }

    fn debug_data(&self) -> Option<&PcgDebugData> {
        match self {
            PcgDomain::Analysis(dataflow_state) => {
                dataflow_state.expect_transfer().debug_data.as_ref()
            }
            PcgDomain::Results(data) => data.debug_data.as_ref(),
            _ => panic!("Expected analysis or results domain, got {:?}", self),
        }
    }

    fn data_mut(&mut self) -> &mut PcgDomainData<'a, 'tcx> {
        match self {
            PcgDomain::Analysis(dataflow_state) => &mut dataflow_state.expect_transfer_mut().data,
            PcgDomain::Results(data) => &mut data.data,
            _ => panic!("Expected analysis or results domain, got {:?}", self),
        }
    }
}

impl<'a, 'tcx: 'a, T> HasPcgDomainData<'a, 'tcx> for DomainDataWithCtxt<'a, 'tcx, T> {
    fn data(&self) -> &PcgDomainData<'a, 'tcx> {
        &self.data
    }

    fn debug_data(&self) -> Option<&PcgDebugData> {
        self.debug_data.as_ref()
    }

    fn data_mut(&mut self) -> &mut PcgDomainData<'a, 'tcx> {
        &mut self.data
    }
}

impl<'a, 'tcx, T> DomainDataWithCtxt<'a, 'tcx, T> {
    pub(crate) fn dot_graphs(&self) -> Option<Rc<RefCell<PcgDotGraphsForBlock>>> {
        self.debug_data.as_ref().map(|data| data.dot_graphs.clone())
    }

    pub(crate) fn register_new_debug_iteration(&mut self, location: mir::Location) {
        if let Some(debug_data) = &mut self.debug_data {
            debug_data
                .dot_graphs
                .borrow_mut()
                .register_new_iteration(location.statement_index);
        }
    }

    pub(crate) fn new(
        data: PcgDomainData<'a, 'tcx>,
        debug_data: Option<PcgDebugData>,
        ctxt: T,
    ) -> Self {
        Self {
            data,
            debug_data,
            ctxt,
        }
    }
}

impl<'a, 'tcx, T> PartialEq for DomainDataWithCtxt<'a, 'tcx, T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<'a, 'tcx, T: Eq> Eq for DomainDataWithCtxt<'a, 'tcx, T> {}

use private::*;

#[derive(From, Clone)]
pub enum PcgDomain<'a, 'tcx> {
    Bottom,
    Error(PcgError),
    Analysis(DataflowState<'a, 'tcx, AnalysisCtxt<'a, 'tcx>>),
    Results(DomainDataWithCtxt<'a, 'tcx, ResultsCtxt<'a, 'tcx>>),
}

impl<'a, 'tcx> Eq for PcgDomain<'a, 'tcx> {}

impl<'a, 'tcx> PartialEq for PcgDomain<'a, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PcgDomain::Bottom, PcgDomain::Bottom) => true,
            (PcgDomain::Error(e1), PcgDomain::Error(e2)) => e1 == e2,
            (PcgDomain::Analysis(d1), PcgDomain::Analysis(d2)) => d1 == d2,
            (PcgDomain::Results(d1), PcgDomain::Results(d2)) => d1 == d2,
            _ => false,
        }
    }
}

impl<'a, 'tcx: 'a> PcgDomain<'a, 'tcx> {
    pub(crate) fn is_results(&self) -> bool {
        matches!(self, PcgDomain::Results(_))
    }

    pub(crate) fn bottom() -> Self {
        Self::Bottom
    }
    pub(crate) fn record_error(&mut self, error: PcgError) {
        *self = Self::Error(error);
    }
    pub(crate) fn data_mut(&mut self) -> &mut PcgDomainData<'a, 'tcx> {
        match self {
            PcgDomain::Analysis(dataflow_state) => &mut dataflow_state.expect_transfer_mut().data,
            PcgDomain::Results(data) => &mut data.data,
            _ => panic!("Expected analysis or results domain, got {:?}", self),
        }
    }
    pub(crate) fn complete(&mut self) {
        let data_with_ctxt = self.expect_analysis_mut().expect_transfer_mut();
        let debug_data = data_with_ctxt.debug_data.take();
        let ctxt = data_with_ctxt.ctxt.bc_ctxt();
        let data = data_with_ctxt.data.clone();
        *self = Self::Results(DomainDataWithCtxt::new(
            data,
            debug_data,
            ResultsCtxt::new(ctxt),
        ));
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ResultsCtxt<'a, 'tcx> {
    ctxt: CompilerCtxt<'a, 'tcx>,
}

impl<'a, 'tcx: 'a> ResultsCtxt<'a, 'tcx> {
    pub(crate) fn new(ctxt: CompilerCtxt<'a, 'tcx>) -> Self {
        Self { ctxt }
    }
}

impl<'a, 'tcx: 'a> HasBorrowCheckerCtxt<'a, 'tcx> for ResultsCtxt<'a, 'tcx> {
    fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, &'a (dyn BorrowCheckerInterface<'tcx>)> {
        self.ctxt
    }

    fn bc(&self) -> &'a (dyn BorrowCheckerInterface<'tcx>) {
        self.ctxt.bc()
    }
}

impl<'a, 'tcx: 'a> HasCompilerCtxt<'a, 'tcx> for ResultsCtxt<'a, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx, ()> {
        self.ctxt.ctxt()
    }
}

impl<'a, 'tcx> CapabilityOps<ResultsCtxt<'a, 'tcx>> for SymbolicCapability<'a> {
    fn minimum(self, other: impl Into<Self>, ctxt: ResultsCtxt<'a, 'tcx>) -> Option<Self> {
        self.expect_concrete()
            .minimum(other.into().expect_concrete())
            .map(SymbolicCapability::Concrete)
    }
}

mod private {
    use std::rc::Rc;

    use derive_more::From;

    use crate::{
        pcg::{
            BodyAnalysis, DataflowStmtPhase, Pcg, PcgDebugData, PcgDomainData, PcgError,
            ResultsCtxt, ctxt::AnalysisCtxt, dot_graphs::ToGraph,
            place_capabilities::SymbolicPlaceCapabilities,
        },
        utils::{CompilerCtxt, domain_data::DomainDataIndex},
    };
}

pub(crate) trait HasPcgDomainData<'a, 'tcx: 'a> {
    fn data(&self) -> &PcgDomainData<'a, 'tcx>;
    fn debug_data(&self) -> Option<&PcgDebugData>;

    fn data_mut(&mut self) -> &mut PcgDomainData<'a, 'tcx>;

    fn pcg(&self, phase: impl Into<DomainDataIndex>) -> &Pcg<'a, 'tcx> {
        &self.data().pcg[phase.into()]
    }

    fn generate_dot_graph(
        &self,
        phase: DataflowStmtPhase,
        location: mir::Location,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) {
        let index = match phase {
            DataflowStmtPhase::EvalStmt(phase) => DomainDataIndex::Eval(phase),
            _ => DomainDataIndex::Initial,
        };
        generate_dot_graph(
            location,
            ToGraph::Phase(phase),
            self.pcg(index).into(),
            self.debug_data(),
            ctxt,
        );
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
        if *PANIC_ON_ERROR {
            panic!("PCG Error: {:?}", error);
        }
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

impl From<PcgUnsupportedError> for PcgError {
    fn from(e: PcgUnsupportedError) -> Self {
        Self::new(PCGErrorKind::Unsupported(e), vec![])
    }
}

impl PcgError {
    pub(crate) fn new(kind: PCGErrorKind, context: Vec<String>) -> Self {
        if *PANIC_ON_ERROR {
            panic!("PCG Error: {:?} ({})", kind, context.join(", "));
        }
        Self { kind, context }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PCGErrorKind {
    Unsupported(PcgUnsupportedError),
    Internal(PcgInternalError),
}

impl PcgError {
    pub(crate) fn internal(msg: String) -> Self {
        Self {
            kind: PCGErrorKind::Internal(PcgInternalError::new(msg)),
            context: vec![],
        }
    }

    pub(crate) fn unsupported(err: PcgUnsupportedError) -> Self {
        Self {
            kind: PCGErrorKind::Unsupported(err),
            context: vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PcgInternalError(String);

impl PcgInternalError {
    pub(crate) fn new(msg: String) -> Self {
        Self(msg)
    }
}

impl From<PcgInternalError> for PcgError {
    fn from(e: PcgInternalError) -> Self {
        PcgError::new(PCGErrorKind::Internal(e), vec![])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PcgUnsupportedError {
    AssignBorrowToNonReferenceType,
    DerefUnsafePtr,
    MoveUnsafePtrWithNestedLifetime,
    ExpansionOfAliasType,
    CallWithUnsafePtrWithNestedLifetime,
    IndexingNonIndexableType,
    InlineAssembly,
    MaxNodesExceeded,
}

impl<'a, 'tcx> PcgDomain<'a, 'tcx> {
    pub(crate) fn error(&self) -> Option<&PcgError> {
        match self {
            PcgDomain::Error(e) => Some(e),
            _ => None,
        }
    }
    pub(crate) fn is_bottom(&self) -> bool {
        matches!(self, PcgDomain::Bottom)
    }

    pub(crate) fn has_error(&self) -> bool {
        match self {
            PcgDomain::Error(_) => true,
            _ => false,
        }
    }
    pub(crate) fn expect_analysis(&self) -> &DataflowState<'a, 'tcx, AnalysisCtxt<'a, 'tcx>> {
        match self {
            PcgDomain::Analysis(dataflow_state) => dataflow_state,
            _ => panic!("Expected analysis domain, got {:?}", self),
        }
    }

    pub(crate) fn expect_analysis_mut(
        &mut self,
    ) -> &mut DataflowState<'a, 'tcx, AnalysisCtxt<'a, 'tcx>> {
        match self {
            PcgDomain::Analysis(dataflow_state) => dataflow_state,
            _ => panic!("Expected analysis domain, got {:?}", self),
        }
    }

    pub(crate) fn expect_results(&self) -> &DomainDataWithCtxt<'a, 'tcx, ResultsCtxt<'a, 'tcx>> {
        match self {
            PcgDomain::Results(dataflow_state) => dataflow_state,
            _ => panic!("Expected results domain, got {:?}", self),
        }
    }
}

impl JoinSemiLattice for PcgDomain<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        if let PcgDomain::Analysis(DataflowState::Pending(pending)) = self {
            pending.push(other.expect_analysis().expect_transfer().clone());
            return true;
        }
        if let PcgDomain::Error(e) = other {
            self.record_error(e.clone());
        }
        return false;
    }
}

impl<'a, 'tcx> DebugWithContext<AnalysisEngine<PcgEngine<'a, 'tcx>>> for PcgDomain<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        _old: &Self,
        _ctxt: &AnalysisEngine<PcgEngine<'a, 'tcx>>,
        _f: &mut Formatter<'_>,
    ) -> std::fmt::Result {
        Ok(())
    }
}
