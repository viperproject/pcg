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
    action::PcgActions, borrow_checker::BorrowCheckerInterface, r#loop::{LoopAnalysis, LoopPlaceUsageAnalysis, PlaceUsages}, pcg::{
        ctxt::AnalysisCtxt, dot_graphs::{generate_dot_graph, PcgDotGraphsForBlock, ToGraph}, place_capabilities::
            SymbolicPlaceCapabilities, CapabilityOps, PcgArena, SymbolicCapability
    }, rustc_interface::{
        middle::mir::{self, BasicBlock},
        mir_dataflow::{fmt::DebugWithContext, move_paths::MoveData, JoinSemiLattice},
    }, utils::{
        arena::PcgArenaRef, domain_data::{DomainData, DomainDataIndex}, eval_stmt_data::EvalStmtData, incoming_states::IncomingStates, initialized::DefinitelyInitialized, liveness::PlaceLiveness, CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, Place, PANIC_ON_ERROR
    }, AnalysisEngine
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

#[derive(Clone)]
pub(crate) struct PcgDebugData {
    pub(crate) dot_output_dir: String,
    pub(crate) dot_graphs: Rc<RefCell<PcgDotGraphsForBlock>>,
}

#[derive(Clone, Eq, Debug)]
pub struct PcgDomainData<'a, 'tcx, Capabilities = SymbolicPlaceCapabilities<'a, 'tcx>> {
    pub(crate) pcg: DomainData<PcgArenaRef<'a, Pcg<'a, 'tcx, Capabilities>>>,
    pub(crate) actions: EvalStmtData<PcgActions<'tcx>>,
}

impl<Capabilities: PartialEq> PartialEq for PcgDomainData<'_, '_, Capabilities> {
    fn eq(&self, other: &Self) -> bool {
        self.pcg == other.pcg
    }
}

impl<'a> PcgDomainData<'a, '_> {
    pub(crate) fn new(arena: PcgArena<'a>) -> Self {
        let pcg = Rc::new_in(Pcg::default(), arena);
        Self {
            pcg: DomainData::new(pcg),
            actions: EvalStmtData::default(),
        }
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
            PcgDomain::Bottom(e) => write!(f, "Bottom({:?})", e),
            PcgDomain::MaybeComplete(d) => write!(f, "MaybeCompleteDomain({:?})", d),
        }
    }
}

#[derive(From, Clone)]
pub enum PcgDomain<'a, 'tcx> {
    Bottom(Option<PcgError>),
    MaybeComplete(MaybeCompleteDomain<'a, 'tcx>),
}

impl PcgDomain<'_, '_> {
    pub(crate) fn record_error(&mut self, error: PcgError) {
        match self {
            PcgDomain::Bottom(pcg_error) => *pcg_error = Some(error),
            PcgDomain::MaybeComplete(maybe_complete_domain) => {
                maybe_complete_domain.record_error(error)
            }
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct ResultsCtxt<'a, 'tcx> {
    ctxt: CompilerCtxt<'a, 'tcx>,
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
            ctxt::AnalysisCtxt, dot_graphs::ToGraph, place_capabilities::SymbolicPlaceCapabilities, BodyAnalysis, DataflowStmtPhase, Pcg, PcgDebugData, PcgDomainData, PcgError, ResultsCtxt
        },
        utils::{domain_data::DomainDataIndex, CompilerCtxt},
    };

    #[derive(From, Clone)]
    pub enum MaybeCompleteDomain<'a, 'tcx> {
        InProgress(InProgressDomain<'a, 'tcx>),
        Complete(CompleteDomain<'a, 'tcx>),
    }

    #[derive(Clone)]
    pub struct PcgDomainT<'a, 'tcx, T> {
        pub(crate) ctxt: T,
        pub(crate) data: std::result::Result<PcgDomainData<'a, 'tcx>, PcgError>,
        pub(crate) debug_data: Option<PcgDebugData>,
    }

    pub(crate) type InProgressDomain<'a, 'tcx> = PcgDomainT<'a, 'tcx, AnalysisCtxt<'a, 'tcx>>;
    pub(crate) type CompleteDomain<'a, 'tcx> = PcgDomainT<'a, 'tcx, ResultsCtxt<'a, 'tcx>>;
}

pub(crate) use private::*;

impl<'a, 'tcx> HasPcgDomainData<'a, 'tcx> for MaybeCompleteDomain<'a, 'tcx> {
    fn data(&self) -> &PcgDomainData<'a, 'tcx> {
        match self {
            MaybeCompleteDomain::InProgress(d) => d.data(),
            MaybeCompleteDomain::Complete(d) => d.data(),
        }
    }

    fn debug_data(&self) -> Option<&PcgDebugData> {
        match self {
            MaybeCompleteDomain::InProgress(d) => d.debug_data(),
            MaybeCompleteDomain::Complete(d) => d.debug_data(),
        }
    }

    fn data_mut(&mut self) -> &mut PcgDomainData<'a, 'tcx> {
        match self {
            MaybeCompleteDomain::InProgress(pcg_domain_t) => pcg_domain_t.data_mut(),
            MaybeCompleteDomain::Complete(pcg_domain_t) => pcg_domain_t.data_mut(),
        }
    }
}

impl<'a, 'tcx> MaybeCompleteDomain<'a, 'tcx> {
    pub(crate) fn debug_data(&self) -> Option<PcgDebugData> {
        match self {
            MaybeCompleteDomain::InProgress(d) => d.debug_data.clone(),
            MaybeCompleteDomain::Complete(d) => d.debug_data.clone(),
        }
    }

    pub(crate) fn data_mut(
        &mut self,
    ) -> std::result::Result<&mut PcgDomainData<'a, 'tcx>, PcgError> {
        match self {
            MaybeCompleteDomain::InProgress(d) => d.data.as_mut().map_err(|e| e.clone()),
            MaybeCompleteDomain::Complete(d) => d.data.as_mut().map_err(|e| e.clone()),
        }
    }

    pub(crate) fn error(&self) -> Option<&PcgError> {
        match self {
            MaybeCompleteDomain::InProgress(d) => d.error(),
            MaybeCompleteDomain::Complete(d) => d.error(),
        }
    }

    pub(crate) fn data(&self) -> std::result::Result<&PcgDomainData<'a, 'tcx>, PcgError> {
        match self {
            MaybeCompleteDomain::InProgress(d) => d.data.as_ref().map_err(|e| e.clone()),
            MaybeCompleteDomain::Complete(d) => d.data.as_ref().map_err(|e| e.clone()),
        }
    }

    pub(crate) fn record_error(&mut self, error: PcgError) {
        match self {
            MaybeCompleteDomain::InProgress(d) => d.record_error(error),
            MaybeCompleteDomain::Complete(d) => d.record_error(error),
        }
    }

    pub(crate) fn in_progress_mut(&mut self) -> Option<&mut InProgressDomain<'a, 'tcx>> {
        match self {
            MaybeCompleteDomain::InProgress(d) => Some(d),
            MaybeCompleteDomain::Complete(_) => None,
        }
    }
}

impl<'a, 'tcx> std::fmt::Debug for MaybeCompleteDomain<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeCompleteDomain::InProgress(d) => {
                write!(f, "InProgressDomain({:?})", d.ctxt.block)
            }
            MaybeCompleteDomain::Complete(_) => write!(f, "CompleteDomain"),
        }
    }
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

impl<'a, 'tcx: 'a, T> HasPcgDomainData<'a, 'tcx> for PcgDomainT<'a, 'tcx, T> {
    fn data(&self) -> &PcgDomainData<'a, 'tcx> {
        &self.data.as_ref().unwrap()
    }

    fn data_mut(&mut self) -> &mut PcgDomainData<'a, 'tcx> {
        self.data.as_mut().unwrap()
    }

    fn debug_data(&self) -> Option<&PcgDebugData> {
        self.debug_data.as_ref()
    }
}

impl<'a, 'tcx> CompleteDomain<'a, 'tcx> {
    pub(crate) fn dot_graphs(&self) -> Option<Rc<RefCell<PcgDotGraphsForBlock>>> {
        self.debug_data.as_ref().map(|data| data.dot_graphs.clone())
    }
    pub(crate) fn error(&self) -> Option<&PcgError> {
        self.data.as_ref().err()
    }

    pub(crate) fn record_error(&mut self, error: PcgError) {
        self.data = Err(error);
    }
}

impl<'a, 'tcx> InProgressDomain<'a, 'tcx> {
    pub(crate) fn block(&self) -> BasicBlock {
        self.ctxt.block.unwrap()
    }

    pub(crate) fn set_block(&mut self, block: BasicBlock) {
        self.ctxt.block = Some(block);
    }

    pub(crate) fn set_debug_data(
        &mut self,
        debug_output_dir: String,
        dot_graphs: Rc<RefCell<PcgDotGraphsForBlock>>,
    ) {
        self.debug_data = Some(PcgDebugData {
            dot_output_dir: debug_output_dir,
            dot_graphs,
        });
    }

    pub(crate) fn record_error(&mut self, error: PcgError) {
        self.data = Err(error);
    }

    pub(crate) fn has_error(&self) -> bool {
        self.data.is_err()
    }

    pub(crate) fn register_new_debug_iteration(&mut self, location: mir::Location) {
        if let Some(debug_data) = &mut self.debug_data {
            debug_data
                .dot_graphs
                .borrow_mut()
                .register_new_iteration(location.statement_index);
        }
    }

    pub(crate) fn error(&self) -> Option<&PcgError> {
        self.data.as_ref().err()
    }

    pub(crate) fn pcg_mut(&mut self, phase: DomainDataIndex) -> &mut Pcg<'a, 'tcx> {
        match &mut self.data {
            Ok(data) => PcgArenaRef::make_mut(&mut data.pcg[phase]),
            Err(e) => panic!("PCG error: {e:?}"),
        }
    }

    pub(crate) fn dot_graphs(&self) -> Option<Rc<RefCell<PcgDotGraphsForBlock>>> {
        self.debug_data.as_ref().map(|data| data.dot_graphs.clone())
    }
}

impl<'a, 'tcx, T> PcgDomainT<'a, 'tcx, T> {
    pub(crate) fn new(
        data: std::result::Result<PcgDomainData<'a, 'tcx>, PcgError>,
        debug_data: Option<PcgDebugData>,
        ctxt: T,
    ) -> Self {
        Self {
            ctxt,
            data,
            debug_data,
        }
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
            PcgDomain::MaybeComplete(maybe_complete) => maybe_complete.error(),
            PcgDomain::Bottom(e) => e.as_ref(),
        }
    }
    pub(crate) fn is_bottom(&self) -> bool {
        matches!(self, PcgDomain::Bottom(_))
    }

    pub(crate) fn is_complete(&self) -> bool {
        matches!(
            self,
            PcgDomain::MaybeComplete(MaybeCompleteDomain::Complete(_))
        )
    }

    pub(crate) fn has_error(&self) -> bool {
        match self {
            PcgDomain::MaybeComplete(MaybeCompleteDomain::Complete(d)) => d.data.is_err(),
            PcgDomain::MaybeComplete(MaybeCompleteDomain::InProgress(d)) => d.data.is_err(),
            PcgDomain::Bottom(e) => e.is_some(),
        }
    }
    pub(crate) fn expect_in_progress(&self) -> &InProgressDomain<'a, 'tcx> {
        match self {
            PcgDomain::MaybeComplete(MaybeCompleteDomain::InProgress(d)) => d,
            _ => panic!("Expected in progress domain, got {:?}", self),
        }
    }

    pub(crate) fn expect_complete(&self) -> &CompleteDomain<'a, 'tcx> {
        match self {
            PcgDomain::MaybeComplete(MaybeCompleteDomain::Complete(d)) => d,
            _ => panic!("Expected complete domain, got {:?}", self),
        }
    }

    pub(crate) fn expect_in_progress_mut(&mut self) -> &mut InProgressDomain<'a, 'tcx> {
        match self {
            PcgDomain::MaybeComplete(MaybeCompleteDomain::InProgress(d)) => d,
            _ => panic!("Expected in progress domain, got {:?}", self),
        }
    }

    pub(crate) fn expect_maybe_complete_mut(&mut self) -> &mut MaybeCompleteDomain<'a, 'tcx> {
        match self {
            PcgDomain::MaybeComplete(maybe_complete) => maybe_complete,
            _ => panic!("Expected maybe complete domain, got {:?}", self),
        }
    }

    pub(crate) fn complete(&mut self) {
        let domain = self.expect_in_progress();
        let results_ctxt = ResultsCtxt {
            ctxt: domain.ctxt.ctxt,
        };
        let complete_domain = CompleteDomain::new(
            domain.data.clone(),
            domain.debug_data.clone(),
            results_ctxt,
        );
        *self = PcgDomain::MaybeComplete(MaybeCompleteDomain::Complete(complete_domain));
    }
}

impl<'a, 'tcx> PcgDomain<'a, 'tcx> {
    pub(crate) fn in_progress_mut(&mut self) -> Option<&mut InProgressDomain<'a, 'tcx>> {
        match self {
            PcgDomain::MaybeComplete(MaybeCompleteDomain::InProgress(d)) => Some(d),
            _ => None,
        }
    }

    pub(crate) fn in_progress(&self) -> Option<&InProgressDomain<'a, 'tcx>> {
        match self {
            PcgDomain::MaybeComplete(MaybeCompleteDomain::InProgress(d)) => Some(d),
            _ => None,
        }
    }
}

impl Eq for PcgDomain<'_, '_> {}

impl PartialEq for PcgDomain<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PcgDomain::Bottom(_), PcgDomain::Bottom(_)) => true,
            (
                PcgDomain::MaybeComplete(MaybeCompleteDomain::Complete(d1)),
                PcgDomain::MaybeComplete(MaybeCompleteDomain::Complete(d2)),
            ) => d1.data == d2.data,
            (
                PcgDomain::MaybeComplete(MaybeCompleteDomain::InProgress(d1)),
                PcgDomain::MaybeComplete(MaybeCompleteDomain::InProgress(d2)),
            ) => d1.data == d2.data,
            _ => false,
        }
    }
}

impl JoinSemiLattice for PcgDomain<'_, '_> {
    // TODO: It should be possible to simplify this logic considerably because
    // each block should only be visited once.
    fn join(&mut self, other: &Self) -> bool {
        let Some(slf) = self.in_progress_mut() else {
            return false;
        };
        let Some(other) = other.in_progress() else {
            return false;
        };
        if other.has_error() && !slf.has_error() {
            slf.data = other.data.clone();
            return true;
        }

        let self_block = slf.block();
        let other_block = other.block();

        let data = match &mut slf.data {
            Ok(data) => data,
            Err(_) => return false,
        };

        let seen = data.pcg.incoming_states.contains(other_block);

        if seen || slf.ctxt.ctxt.is_back_edge(other_block, self_block) {
            return false;
        }

        let is_loop_head = slf.ctxt.body_analysis.is_loop_head(self_block);

        let first_join = data.pcg.incoming_states.is_empty();

        if first_join || seen {
            // Either this is the first time we're joining the block (and we
            // should inherit the existing state) or we're seeing the same block
            // for the first time again.
            // In either case, we should inherit the state from the other block.
            data.pcg.incoming_states = IncomingStates::singleton(other_block);

            let other_state = &other.data.as_ref().unwrap().pcg.states[EvalStmtPhase::PostMain];
            data.pcg.entry_state = other_state.clone();
            let entry_state_mut = PcgArenaRef::make_mut(&mut data.pcg.entry_state);
            entry_state_mut
                .borrow
                .add_cfg_edge(other_block, self_block, slf.ctxt.ctxt);

            if !is_loop_head {
                return true;
            }
        } else {
            data.pcg.incoming_states.insert(other_block);
        }

        let pcg =
            PcgArenaRef::make_mut(&mut slf.data.as_mut().unwrap().pcg[DomainDataIndex::Initial]);
        let result = match pcg.join(
            other.pcg(DomainDataIndex::Eval(EvalStmtPhase::PostMain)),
            self_block,
            other_block,
            slf.ctxt,
        ) {
            Ok(changed) => changed,
            Err(e) => {
                slf.record_error(e);
                false
            }
        };
        if slf.debug_data.is_some() {
            slf.register_new_debug_iteration(mir::Location {
                block: self_block,
                statement_index: 0,
            });
            slf.generate_dot_graph(
                DataflowStmtPhase::Join(other.block()),
                mir::Location {
                    block: self_block,
                    statement_index: 0,
                },
                slf.ctxt,
            );
        }
        result
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
