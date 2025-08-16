// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cell::RefCell,
    fmt::{Debug, Formatter},
    rc::Rc,
};

use derive_more::From;

use crate::{
    AnalysisEngine,
    action::PcgActions,
    error::PcgError,
    r#loop::{LoopAnalysis, LoopPlaceUsageAnalysis, PlaceUsages},
    pcg::{
        ctxt::AnalysisCtxt, dot_graphs::PcgDotGraphsForBlock,
        place_capabilities::SymbolicPlaceCapabilities,
    },
    pcg_validity_assert,
    rustc_interface::{
        middle::mir::{self, BasicBlock},
        mir_dataflow::{JoinSemiLattice, fmt::DebugWithContext, move_paths::MoveData},
    },
    utils::{
        CompilerCtxt, DataflowCtxt, HasBorrowCheckerCtxt, PANIC_ON_ERROR, Place, ToGraph,
        arena::PcgArenaRef,
        domain_data::{DomainData, DomainDataIndex},
        eval_stmt_data::EvalStmtData,
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

#[derive(Copy, Clone)]
pub struct DataflowIterationDebugInfo {
    pub join_with: BasicBlock,
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct PcgBlockDebugVisualizationGraphs<'a> {
    #[allow(dead_code)]
    block: BasicBlock,
    pub(crate) dot_output_dir: &'a str,
    pub(crate) dot_graphs: &'a RefCell<PcgDotGraphsForBlock>,
}

impl<'a> PcgBlockDebugVisualizationGraphs<'a> {
    pub(crate) fn new(
        block: BasicBlock,
        dot_output_dir: &'a str,
        dot_graphs: &'a RefCell<PcgDotGraphsForBlock>,
    ) -> Self {
        Self {
            block,
            dot_output_dir,
            dot_graphs,
        }
    }
}

#[derive(Clone, Eq, Debug)]
pub struct PcgDomainData<'a, 'tcx, Capabilities = SymbolicPlaceCapabilities<'tcx>> {
    pub(crate) pcg: DomainData<PcgArenaRef<'a, Pcg<'tcx, Capabilities>>>,
    pub(crate) actions: EvalStmtData<PcgActions<'tcx>>,
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

mod private {
    use derive_more::From;

    use crate::borrow_checker::BorrowCheckerInterface;
    use crate::pcg::DomainDataWithCtxt;
    use crate::utils::{CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt};

    #[derive(Clone, From, Eq)]
    pub struct PendingDataflowState<'a, 'tcx, T> {
        pending: Vec<DomainDataWithCtxt<'a, 'tcx, T>>,
    }

    impl<T> PartialEq for PendingDataflowState<'_, '_, T> {
        fn eq(&self, other: &Self) -> bool {
            self.pending == other.pending
        }
    }

    impl<T> Default for PendingDataflowState<'_, '_, T> {
        fn default() -> Self {
            Self { pending: vec![] }
        }
    }

    impl<'a, 'tcx, T> PendingDataflowState<'a, 'tcx, T> {
        pub(crate) fn take_first(
            self,
        ) -> (
            DomainDataWithCtxt<'a, 'tcx, T>,
            Vec<DomainDataWithCtxt<'a, 'tcx, T>>,
        ) {
            let mut iter = self.pending.into_iter();
            (iter.next().unwrap(), iter.collect())
        }

        pub(crate) fn take(&mut self) -> Self {
            std::mem::take(self)
        }

        pub(crate) fn push(&mut self, data: DomainDataWithCtxt<'a, 'tcx, T>) -> bool {
            if self.pending.iter().any(|d| d == &data) {
                return false;
            }
            self.pending.push(data);
            true
        }
    }

    #[derive(Clone, Copy, Debug)]
    pub struct ResultsCtxt<'a, 'tcx> {
        ctxt: CompilerCtxt<'a, 'tcx>,
    }

    impl<'a, 'tcx: 'a> ResultsCtxt<'a, 'tcx> {
        pub(crate) fn new(ctxt: CompilerCtxt<'a, 'tcx>) -> Self {
            Self { ctxt }
        }
    }

    impl<'a, 'tcx: 'a> HasBorrowCheckerCtxt<'a, 'tcx> for ResultsCtxt<'a, 'tcx> {
        fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>> {
            self.ctxt
        }

        fn bc(&self) -> &'a dyn BorrowCheckerInterface<'tcx> {
            self.ctxt.bc()
        }
    }

    impl<'a, 'tcx: 'a> HasCompilerCtxt<'a, 'tcx> for ResultsCtxt<'a, 'tcx> {
        fn ctxt(&self) -> CompilerCtxt<'a, 'tcx, ()> {
            self.ctxt.ctxt()
        }
    }
}

pub(crate) use private::*;

impl<'a, 'tcx> PendingDataflowState<'a, 'tcx, AnalysisCtxt<'a, 'tcx>> {
    pub(crate) fn join(
        self,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Result<DomainDataWithCtxt<'a, 'tcx, AnalysisCtxt<'a, 'tcx>>, PcgError> {
        let (first, rest) = self.take_first();
        let mut result: DomainDataWithCtxt<'a, 'tcx, AnalysisCtxt<'a, 'tcx>> =
            DomainDataWithCtxt::new(PcgDomainData::from_incoming(ctxt.block, &first), ctxt);
        let curr = Rc::make_mut(&mut result.data.pcg.entry_state);
        if ctxt.body_analysis.is_loop_head(ctxt.block) {
            curr.join(
                &first.data.pcg.states.0.post_main,
                ctxt.block,
                first.ctxt.block,
                result.ctxt,
            )?;
        }
        for other in rest {
            if !ctxt.ctxt.is_back_edge(other.ctxt.block, ctxt.block) {
                curr.join(
                    &other.data.pcg.states.0.post_main,
                    ctxt.block,
                    other.ctxt.block,
                    result.ctxt,
                )?;
            }
        }
        Ok(result)
    }
}

#[derive(Clone)]
pub enum DataflowState<'a, 'tcx, T> {
    Pending(PendingDataflowState<'a, 'tcx, T>),
    Transfer(DomainDataWithCtxt<'a, 'tcx, T>),
}

impl<'a, 'tcx> DataflowState<'a, 'tcx, AnalysisCtxt<'a, 'tcx>> {
    pub(crate) fn ensure_transfer(
        &mut self,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Result<&mut DomainDataWithCtxt<'a, 'tcx, AnalysisCtxt<'a, 'tcx>>, PcgError> {
        match self {
            DataflowState::Pending(pending_state) => {
                let pending_state = pending_state.take();
                *self = DataflowState::Transfer(pending_state.join(ctxt)?);
                Ok(self.expect_transfer_mut())
            }
            DataflowState::Transfer(domain_data_with_ctxt) => Ok(domain_data_with_ctxt),
        }
    }

    pub(crate) fn take_into_data(
        self,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Result<DomainDataWithCtxt<'a, 'tcx, AnalysisCtxt<'a, 'tcx>>, PcgError> {
        match self {
            DataflowState::Pending(pending) => Ok(pending.join(ctxt)?),
            DataflowState::Transfer(transfer) => Ok(transfer),
        }
    }
}
impl<'a, 'tcx, T> DataflowState<'a, 'tcx, T> {
    pub(crate) fn expect_pending_mut(&mut self) -> &mut PendingDataflowState<'a, 'tcx, T> {
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

impl<T> PartialEq for DataflowState<'_, '_, T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (DataflowState::Pending(d1), DataflowState::Pending(d2)) => d1 == d2,
            (DataflowState::Transfer(d1), DataflowState::Transfer(d2)) => d1 == d2,
            _ => false,
        }
    }
}

impl<T> Eq for DataflowState<'_, '_, T> {}

impl<T> std::fmt::Debug for DataflowState<'_, '_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DataflowState::Pending(_) => write!(f, "Pending"),
            DataflowState::Transfer(_) => write!(f, "Transfer"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct DomainDataWithCtxt<'a, 'tcx, T> {
    pub(crate) ctxt: T,
    pub(crate) data: PcgDomainData<'a, 'tcx>,
}

impl<'a, 'tcx: 'a> HasPcgDomainData<'a, 'tcx> for PcgDomain<'a, 'tcx> {
    fn data(&self) -> &PcgDomainData<'a, 'tcx> {
        match self {
            PcgDomain::Analysis(dataflow_state) => &dataflow_state.expect_transfer().data,
            PcgDomain::Results(data) => &data.data,
            _ => panic!("Expected analysis or results domain, got {:?}", self),
        }
    }
}

impl<'a, 'tcx: 'a, T> HasPcgDomainData<'a, 'tcx> for DomainDataWithCtxt<'a, 'tcx, T> {
    fn data(&self) -> &PcgDomainData<'a, 'tcx> {
        &self.data
    }
}

impl<'a, 'tcx: 'a> DomainDataWithCtxt<'a, 'tcx, AnalysisCtxt<'a, 'tcx>> {
    fn into_results(self) -> DomainDataWithCtxt<'a, 'tcx, ResultsCtxt<'a, 'tcx>> {
        DomainDataWithCtxt::new(self.data, ResultsCtxt::new(self.ctxt.bc_ctxt()))
    }
}

impl<'a, 'tcx, T> DomainDataWithCtxt<'a, 'tcx, T> {
    pub(crate) fn new(data: PcgDomainData<'a, 'tcx>, ctxt: T) -> Self {
        Self { data, ctxt }
    }
}

impl<T> PartialEq for DomainDataWithCtxt<'_, '_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: Eq> Eq for DomainDataWithCtxt<'_, '_, T> {}

#[derive(From, Clone)]
pub enum PcgDomain<'a, 'tcx> {
    Bottom,
    Error(PcgError),
    Analysis(DataflowState<'a, 'tcx, AnalysisCtxt<'a, 'tcx>>),
    Results(DomainDataWithCtxt<'a, 'tcx, ResultsCtxt<'a, 'tcx>>),
}

impl Eq for PcgDomain<'_, '_> {}

impl PartialEq for PcgDomain<'_, '_> {
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

    pub(crate) fn take(&mut self) -> PcgDomain<'a, 'tcx> {
        std::mem::replace(self, PcgDomain::Bottom)
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
    pub(crate) fn complete(&mut self, ctxt: AnalysisCtxt<'a, 'tcx>) {
        if self.is_bottom() || self.is_error() {
            return;
        }
        let domain = self.take();
        *self = PcgDomain::Results(
            domain
                .take_analysis()
                .take_into_data(ctxt)
                .unwrap()
                .into_results(),
        );
    }
}

impl<'a, 'tcx: 'a> DataflowCtxt<'a, 'tcx> for ResultsCtxt<'a, 'tcx> {
    fn try_into_analysis_ctxt(self) -> Option<AnalysisCtxt<'a, 'tcx>> {
        None
    }
}

pub(crate) trait HasPcgDomainData<'a, 'tcx: 'a> {
    fn data(&self) -> &PcgDomainData<'a, 'tcx>;

    fn pcg<'slf>(&'slf self, phase: impl Into<DomainDataIndex>) -> &'slf Pcg<'tcx>
    where
        'a: 'slf,
    {
        &self.data().pcg[phase.into()]
    }

    fn generate_dot_graph(
        &self,
        phase: DataflowStmtPhase,
        location: mir::Location,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) {
        let index = match phase {
            DataflowStmtPhase::EvalStmt(phase) => DomainDataIndex::Eval(phase),
            _ => DomainDataIndex::Initial,
        };
        ctxt.generate_pcg_debug_visualization_graph(
            location,
            ToGraph::Phase(phase),
            self.pcg(index).into(),
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

    pub(crate) fn is_error(&self) -> bool {
        matches!(self, PcgDomain::Error(_))
    }

    pub(crate) fn take_analysis(self) -> DataflowState<'a, 'tcx, AnalysisCtxt<'a, 'tcx>> {
        match self {
            PcgDomain::Analysis(dataflow_state) => dataflow_state,
            _ => panic!("Expected analysis domain, got {:?}", self),
        }
    }

    pub(crate) fn expect_results_or_error(
        &self,
    ) -> Result<&DomainDataWithCtxt<'a, 'tcx, ResultsCtxt<'a, 'tcx>>, PcgError> {
        match self {
            PcgDomain::Results(dataflow_state) => Ok(dataflow_state),
            PcgDomain::Error(pcg_error) => Err(pcg_error.clone()),
            _ => panic!("Expected results or error domain, got {:?}", self),
        }
    }
}

impl JoinSemiLattice for PcgDomain<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        match other {
            PcgDomain::Bottom => false,
            PcgDomain::Error(e) => {
                self.record_error(e.clone());
                false
            }
            PcgDomain::Analysis(dataflow_state) => {
                let other = dataflow_state.expect_transfer();
                match self {
                    PcgDomain::Bottom => {
                        *self =
                            PcgDomain::Analysis(DataflowState::Pending(vec![other.clone()].into()));
                        true
                    }
                    PcgDomain::Error(_) => false,
                    PcgDomain::Analysis(dataflow_state) => {
                        let self_dataflow_state = dataflow_state.expect_pending_mut();
                        self_dataflow_state.push(other.clone());
                        false
                    }
                    PcgDomain::Results(_) => unreachable!(),
                }
            }
            PcgDomain::Results(_) => unreachable!(),
        }
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
