// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    alloc::Allocator,
    cell::RefCell,
    fmt::{Debug, Formatter},
    rc::Rc,
};

use derive_more::TryInto;
use serde::{Serialize, Serializer};

use crate::{
    action::PcgActions,
    borrow_pcg::{
        graph::BorrowsGraph,
        state::{BorrowStateMutRef, BorrowStateRef, BorrowsState, BorrowsStateLike},
    },
    borrows_imgcat_debug,
    pcg::{
        dot_graphs::{generate_dot_graph, PcgDotGraphsForBlock, ToGraph},
        triple::Triple,
    },
    r#loop::{LoopAnalysis, LoopPlaceUsageAnalysis},
    rustc_interface::{
        middle::mir::{self, BasicBlock},
        mir_dataflow::{fmt::DebugWithContext, move_paths::MoveData, JoinSemiLattice},
    },
    utils::{
        arena::ArenaRef,
        data_structures::HashSet,
        domain_data::{DomainData, DomainDataIndex},
        eval_stmt_data::EvalStmtData,
        incoming_states::IncomingStates,
        initialized::DefinitelyInitialized,
        liveness::PlaceLiveness,
        validity::HasValidityCheck,
        CompilerCtxt, Place, CHECK_CYCLES, PANIC_ON_ERROR,
    },
    validity_checks_enabled, validity_checks_warn_only,
    visualization::{dot_graph::DotGraph, generate_pcg_dot_graph},
    AnalysisEngine, DebugLines,
};

use super::{place_capabilities::PlaceCapabilities, PcgEngine};
use crate::free_pcs::OwnedPcg;

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

impl Serialize for EvalStmtPhase {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl EvalStmtPhase {
    pub fn is_operands_stage(&self) -> bool {
        matches!(
            self,
            EvalStmtPhase::PreOperands | EvalStmtPhase::PostOperands
        )
    }

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

#[derive(PartialEq, Eq, Copy, Clone, Debug, Ord, PartialOrd, TryInto)]
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

impl std::fmt::Display for DataflowStmtPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DataflowStmtPhase::Initial => write!(f, "initial"),
            DataflowStmtPhase::EvalStmt(phase) => write!(f, "{phase}"),
            DataflowStmtPhase::Join(block) => write!(f, "join {block:?}"),
        }
    }
}
impl DataflowStmtPhase {
    pub(crate) fn to_filename_str_part(self) -> String {
        self.to_string()
    }
}

impl Serialize for DataflowStmtPhase {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_filename_str_part())
    }
}

#[derive(Clone)]
pub(crate) struct PcgDebugData {
    pub(crate) dot_output_dir: String,
    pub(crate) dot_graphs: Rc<RefCell<PcgDotGraphsForBlock>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Pcg<'tcx> {
    pub(crate) owned: OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowsState<'tcx>,
    pub(crate) capabilities: PlaceCapabilities<'tcx>,
}

impl<'tcx> HasValidityCheck<'tcx> for Pcg<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> std::result::Result<(), String> {
        self.as_ref().check_validity(ctxt)
    }
}

#[derive(Clone, Copy)]
pub(crate) struct PcgRef<'pcg, 'tcx> {
    pub(crate) owned: &'pcg OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowStateRef<'pcg, 'tcx>,
    pub(crate) capabilities: &'pcg PlaceCapabilities<'tcx>,
}

impl<'pcg, 'tcx> From<&'pcg Pcg<'tcx>> for PcgRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg Pcg<'tcx>) -> Self {
        Self {
            owned: &pcg.owned,
            borrow: pcg.borrow.as_ref(),
            capabilities: &pcg.capabilities,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg PcgMutRef<'pcg, 'tcx>> for PcgRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg PcgMutRef<'pcg, 'tcx>) -> Self {
        let borrow = pcg.borrow.as_ref();
        Self {
            owned: &*pcg.owned,
            borrow,
            capabilities: &*pcg.capabilities,
        }
    }
}

pub(crate) struct PcgMutRef<'pcg, 'tcx> {
    pub(crate) owned: &'pcg mut OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowStateMutRef<'pcg, 'tcx>,
    pub(crate) capabilities: &'pcg mut PlaceCapabilities<'tcx>,
}

impl<'pcg, 'tcx> PcgMutRef<'pcg, 'tcx> {
    pub(crate) fn new(
        owned: &'pcg mut OwnedPcg<'tcx>,
        borrow: BorrowStateMutRef<'pcg, 'tcx>,
        capabilities: &'pcg mut PlaceCapabilities<'tcx>,
    ) -> Self {
        Self {
            owned,
            borrow,
            capabilities,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg mut Pcg<'tcx>> for PcgMutRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg mut Pcg<'tcx>) -> Self {
        Self::new(
            &mut pcg.owned,
            (&mut pcg.borrow).into(),
            &mut pcg.capabilities,
        )
    }
}

impl<'tcx> PcgMutRef<'_, 'tcx> {
    pub(crate) fn leaf_places_where(
        &self,
        predicate: impl Fn(Place<'tcx>) -> bool,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<Place<'tcx>> {
        let mut places: HashSet<Place<'tcx>> = self
            .borrow
            .leaf_nodes(ctxt)
            .into_iter()
            .flat_map(|node| node.as_current_place())
            .filter(|p| predicate(*p))
            .collect();

        let mut owned_leaf_places = self
            .owned
            .leaf_places(ctxt)
            .into_iter()
            .filter(|p| predicate(*p))
            .peekable();

        if owned_leaf_places.peek().is_none() {
            return places;
        }

        let owned_places_in_borrow_pcg = self.borrow.graph().owned_places(ctxt);

        for place in owned_leaf_places {
            if !owned_places_in_borrow_pcg.contains(&place) {
                places.insert(place);
            }
        }

        places
    }

    pub(crate) fn assert_validity_at_location(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
        _location: mir::Location,
    ) {
        if validity_checks_enabled()
            && let Err(err) = self.as_ref().check_validity(ctxt)
        {
            // if borrows_imgcat_debug() {
            //     self.render_debug_graph(ctxt, location, "Validity check failed");
            // }
            if validity_checks_warn_only() {
                tracing::error!("Validity check failed: {}", err.to_string());
            } else {
                panic!("Validity check failed: {}", err);
            }
        }
    }
}

pub(crate) trait PcgRefLike<'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx>;
    fn borrows_graph(&self) -> &BorrowsGraph<'tcx> {
        self.as_ref().borrow.graph
    }
    fn is_acyclic(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.borrows_graph().frozen_graph().is_acyclic(ctxt)
    }
}

impl<'tcx> PcgRefLike<'tcx> for PcgMutRef<'_, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx> {
        PcgRef::from(self)
    }
}

impl<'tcx> PcgRefLike<'tcx> for Pcg<'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx> {
        PcgRef::from(self)
    }
}

impl<'tcx> PcgRefLike<'tcx> for PcgRef<'_, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx> {
        *self
    }
}

pub(crate) trait PcgMutRefLike<'pcg, 'tcx: 'pcg> {
    fn as_mut_ref(&'pcg mut self) -> PcgMutRef<'pcg, 'tcx>;
}

impl<'pcg, 'tcx: 'pcg> PcgMutRefLike<'pcg, 'tcx> for PcgMutRef<'pcg, 'tcx> {
    fn as_mut_ref(&'pcg mut self) -> PcgMutRef<'pcg, 'tcx> {
        PcgMutRef {
            owned: self.owned,
            borrow: self.borrow.as_mut_ref(),
            capabilities: self.capabilities,
        }
    }
}

impl<'pcg, 'tcx: 'pcg> PcgMutRefLike<'pcg, 'tcx> for Pcg<'tcx> {
    fn as_mut_ref(&'pcg mut self) -> PcgMutRef<'pcg, 'tcx> {
        self.into()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for PcgRef<'_, 'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> std::result::Result<(), String> {
        self.capabilities.check_validity(ctxt)?;
        self.borrow.check_validity(ctxt)?;
        if *CHECK_CYCLES && !self.is_acyclic(ctxt) {
            return Err("PCG is not acyclic".to_string());
        }
        Ok(())
    }
}

impl<'mir, 'tcx: 'mir> Pcg<'tcx> {
    #[allow(unused)]
    pub(crate) fn render_debug_graph(
        &self,
        ctxt: CompilerCtxt<'mir, 'tcx>,
        location: mir::Location,
        comment: &str,
    ) {
        if borrows_imgcat_debug() {
            let dot_graph = generate_pcg_dot_graph(self.as_ref(), ctxt, location).unwrap();
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }

    pub fn capabilities(&self) -> &PlaceCapabilities<'tcx> {
        &self.capabilities
    }

    pub fn owned_pcg(&self) -> &OwnedPcg<'tcx> {
        &self.owned
    }

    pub fn borrow_pcg(&self) -> &BorrowsState<'tcx> {
        &self.borrow
    }

    pub(crate) fn owned_ensures(&mut self, t: Triple<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) {
        self.owned
            .locals_mut()
            .ensures(t, &mut self.capabilities, ctxt);
    }

    #[tracing::instrument(skip(self, other, ctxt, body_analysis))]
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        body_analysis: &BodyAnalysis<'mir, 'tcx>,
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
        // TODO: This should happen in the borrow join
        other.borrow.add_cfg_edge(other_block, self_block, ctxt);
        res |= self.capabilities.join(&other.capabilities);
        res |= self.borrow.join(
            &other.borrow,
            self_block,
            other_block,
            body_analysis,
            &mut self.capabilities,
            &mut self.owned,
            ctxt,
        )?;
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

impl<A: Allocator> PartialEq for PcgDomainData<'_, A> {
    fn eq(&self, other: &Self) -> bool {
        self.pcg == other.pcg
    }
}

impl<A: Allocator + Clone> PcgDomainData<'_, A> {
    pub(crate) fn new(arena: A) -> Self {
        let pcg = ArenaRef::new_in(Pcg::default(), arena);
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
    ) -> Option<&HashSet<Place<'tcx>>> {
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

#[derive(Clone)]
pub struct PcgDomain<'a, 'tcx, A: Allocator> {
    ctxt: CompilerCtxt<'a, 'tcx>,
    pub(crate) block: Option<BasicBlock>,
    pub(crate) body_analysis: Rc<BodyAnalysis<'a, 'tcx>>,
    pub(crate) data: std::result::Result<PcgDomainData<'tcx, A>, PcgError>,
    pub(crate) debug_data: Option<PcgDebugData>,
    pub(crate) reachable: bool,
}

impl<A: Allocator + Debug> Debug for PcgDomain<'_, '_, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.data)
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

impl<'tcx, A: Allocator> PcgDomain<'_, 'tcx, A> {
    pub(crate) fn has_error(&self) -> bool {
        self.data.is_err()
    }
    pub(crate) fn block(&self) -> BasicBlock {
        self.block.unwrap()
    }
    pub(crate) fn is_initialized(&self) -> bool {
        self.block.is_some()
    }
    pub(crate) fn record_error(&mut self, error: PcgError) {
        self.data = Err(error);
    }
    pub(crate) fn register_new_debug_iteration(&mut self, location: mir::Location) {
        if let Some(debug_data) = &mut self.debug_data {
            debug_data
                .dot_graphs
                .borrow_mut()
                .register_new_iteration(location.statement_index);
        }
    }

    pub(crate) fn generate_dot_graph(&self, phase: DataflowStmtPhase, statement_index: usize) {
        let pcg: &Pcg<'tcx> = match phase {
            DataflowStmtPhase::EvalStmt(phase) => self.pcg(DomainDataIndex::Eval(phase)),
            _ => self.pcg(DomainDataIndex::Initial),
        };
        generate_dot_graph(
            self.block(),
            statement_index,
            ToGraph::Phase(phase),
            pcg.into(),
            self.debug_data.as_ref(),
            self.ctxt,
        );
    }

    pub(crate) fn set_debug_data(
        &mut self,
        output_dir: String,
        dot_graphs: Rc<RefCell<PcgDotGraphsForBlock>>,
    ) {
        self.debug_data = Some(PcgDebugData {
            dot_output_dir: output_dir,
            dot_graphs,
        });
    }

    pub fn pcg(&self, phase: impl Into<DomainDataIndex>) -> &Pcg<'tcx> {
        match &self.data {
            Ok(data) => &data.pcg[phase.into()],
            Err(e) => panic!("PCG error: {e:?}"),
        }
    }

    pub(crate) fn set_block(&mut self, block: BasicBlock) {
        self.block = Some(block);
    }
}

impl<'a, 'tcx, A: Allocator + Clone> PcgDomain<'a, 'tcx, A> {
    pub(crate) fn error(&self) -> Option<&PcgError> {
        self.data.as_ref().err()
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

    pub(crate) fn dot_graphs(&self) -> Option<Rc<RefCell<PcgDotGraphsForBlock>>> {
        self.debug_data.as_ref().map(|data| data.dot_graphs.clone())
    }

    pub(crate) fn new(
        body_analysis: Rc<BodyAnalysis<'a, 'tcx>>,
        repacker: CompilerCtxt<'a, 'tcx>,
        block: Option<BasicBlock>,
        debug_data: Option<PcgDebugData>,
        arena: A,
    ) -> Self {
        Self {
            ctxt: repacker,
            block,
            body_analysis,
            data: Ok(PcgDomainData::new(arena)),
            debug_data,
            reachable: false,
        }
    }
}

impl<A: Allocator + Clone> Eq for PcgDomain<'_, '_, A> {}

impl<A: Allocator + Clone> PartialEq for PcgDomain<'_, '_, A> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<A: Allocator + Clone> JoinSemiLattice for PcgDomain<'_, '_, A> {
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

        if seen || self.ctxt.is_back_edge(other_block, self_block) {
            return false;
        }

        let is_loop_head = self.body_analysis.is_loop_head(self_block);

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

            if !is_loop_head {
                return true;
            }
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
            &self.body_analysis,
            self.ctxt,
        ) {
            Ok(changed) => changed,
            Err(e) => {
                self.record_error(e);
                false
            }
        };
        if self.debug_data.is_some() {
            self.register_new_debug_iteration(mir::Location {
                block: self_block,
                statement_index: 0,
            });
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
    ) -> std::fmt::Result {
        Ok(())
    }
}
