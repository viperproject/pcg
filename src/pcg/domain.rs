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
    AnalysisEngine, DebugLines,
    action::PcgActions,
    borrow_pcg::{
        edge::{borrow::BorrowEdge, kind::BorrowPcgEdgeKind},
        graph::{BorrowsGraph, join::JoinBorrowsArgs},
        state::{BorrowStateMutRef, BorrowStateRef, BorrowsState, BorrowsStateLike},
    },
    borrows_imgcat_debug,
    r#loop::{LoopAnalysis, LoopPlaceUsageAnalysis, PlaceUsages},
    owned_pcg::join::data::JoinOwnedData,
    pcg::{
        CapabilityKind, PcgArena,
        ctxt::AnalysisCtxt,
        dot_graphs::{PcgDotGraphsForBlock, ToGraph, generate_dot_graph},
        place_capabilities::{PlaceCapabilitiesReader, SymbolicPlaceCapabilities},
        triple::Triple,
    },
    rustc_interface::{
        middle::mir::{self, BasicBlock},
        mir_dataflow::{JoinSemiLattice, fmt::DebugWithContext, move_paths::MoveData},
    },
    utils::{
        CHECK_CYCLES, CompilerCtxt, DebugImgcat, HasBorrowCheckerCtxt, PANIC_ON_ERROR, Place,
        arena::PcgArenaRef,
        data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
        domain_data::{DomainData, DomainDataIndex},
        eval_stmt_data::EvalStmtData,
        incoming_states::IncomingStates,
        initialized::DefinitelyInitialized,
        liveness::PlaceLiveness,
        maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
    visualization::{dot_graph::DotGraph, generate_pcg_dot_graph},
};

use super::PcgEngine;
use crate::owned_pcg::OwnedPcg;

#[derive(Copy, Clone)]
pub struct DataflowIterationDebugInfo {
    pub join_with: BasicBlock,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Ord, PartialOrd, Hash)]
pub enum EvalStmtPhase {
    PreOperands,
    PostOperands,
    PreMain,
    PostMain,
}

impl EvalStmtPhase {
    pub(crate) const fn first() -> Self {
        EvalStmtPhase::PreOperands
    }

    pub const fn last() -> Self {
        EvalStmtPhase::PostMain
    }
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
pub struct Pcg<'a, 'tcx, Capabilities = SymbolicPlaceCapabilities<'a, 'tcx>> {
    pub(crate) owned: OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowsState<'tcx>,
    pub(crate) capabilities: Capabilities,
    pub(crate) _marker: PhantomData<&'a ()>,
}

impl<'tcx> HasValidityCheck<'tcx> for Pcg<'_, 'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> std::result::Result<(), String> {
        self.as_ref().check_validity(ctxt)
    }
}

#[derive(Clone, Copy)]
pub(crate) struct PcgRef<'pcg, 'a, 'tcx> {
    pub(crate) owned: &'pcg OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowStateRef<'pcg, 'tcx>,
    pub(crate) capabilities: &'pcg SymbolicPlaceCapabilities<'a, 'tcx>,
}

impl<'a, 'tcx: 'a> PcgRef<'_, 'a, 'tcx> {
    pub(crate) fn render_debug_graph<'slf>(
        &'slf self,
        location: mir::Location,
        debug_imgcat: Option<DebugImgcat>,
        comment: &str,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) {
        if borrows_imgcat_debug(location.block, debug_imgcat) {
            let dot_graph = generate_pcg_dot_graph(self.as_ref(), ctxt, location).unwrap();
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }
}

impl<'pcg, 'a, 'tcx> From<&'pcg Pcg<'a, 'tcx>> for PcgRef<'pcg, 'a, 'tcx> {
    fn from(pcg: &'pcg Pcg<'a, 'tcx>) -> Self {
        Self {
            owned: &pcg.owned,
            borrow: pcg.borrow.as_ref(),
            capabilities: &pcg.capabilities,
        }
    }
}

impl<'pcg, 'a, 'tcx> From<&'pcg PcgMutRef<'pcg, 'a, 'tcx>> for PcgRef<'pcg, 'a, 'tcx> {
    fn from(pcg: &'pcg PcgMutRef<'pcg, 'a, 'tcx>) -> Self {
        let borrow = pcg.borrow.as_ref();
        Self {
            owned: &*pcg.owned,
            borrow,
            capabilities: &*pcg.capabilities,
        }
    }
}

pub(crate) struct PcgMutRef<'pcg, 'a, 'tcx> {
    pub(crate) owned: &'pcg mut OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowStateMutRef<'pcg, 'tcx>,
    pub(crate) capabilities: &'pcg mut SymbolicPlaceCapabilities<'a, 'tcx>,
}

impl<'pcg, 'a, 'tcx> PcgMutRef<'pcg, 'a, 'tcx> {
    pub(crate) fn new(
        owned: &'pcg mut OwnedPcg<'tcx>,
        borrow: BorrowStateMutRef<'pcg, 'tcx>,
        capabilities: &'pcg mut SymbolicPlaceCapabilities<'a, 'tcx>,
    ) -> Self {
        Self {
            owned,
            borrow,
            capabilities,
        }
    }
}

impl<'pcg, 'a, 'tcx> From<&'pcg mut Pcg<'a, 'tcx>> for PcgMutRef<'pcg, 'a, 'tcx> {
    fn from(pcg: &'pcg mut Pcg<'a, 'tcx>) -> Self {
        Self::new(
            &mut pcg.owned,
            (&mut pcg.borrow).into(),
            &mut pcg.capabilities,
        )
    }
}

pub(crate) trait PcgRefLike<'tcx> {
    fn as_ref(&self) -> PcgRef<'_, '_, 'tcx>;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx> {
        self.as_ref().borrow.graph
    }

    fn is_acyclic(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.borrows_graph().frozen_graph().is_acyclic(ctxt)
    }

    fn owned_pcg(&self) -> &OwnedPcg<'tcx> {
        self.as_ref().owned
    }

    fn leaf_places<'a>(&self, ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        let mut leaf_places = self.owned_pcg().leaf_places(ctxt);
        leaf_places.retain(|p| !self.borrows_graph().places(ctxt).contains(p));
        leaf_places.extend(self.borrows_graph().leaf_places(ctxt));
        leaf_places
    }

    fn is_leaf_place<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.leaf_places(ctxt).contains(&place)
    }
}

impl<'a, 'tcx> PcgRefLike<'tcx> for PcgMutRef<'_, 'a, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'a, 'tcx> {
        PcgRef::from(self)
    }
}

impl<'a, 'tcx> PcgRefLike<'tcx> for Pcg<'a, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'a, 'tcx> {
        PcgRef::from(self)
    }
}

impl<'a, 'tcx> PcgRefLike<'tcx> for PcgRef<'_, 'a, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'a, 'tcx> {
        *self
    }
}

impl<'tcx> HasValidityCheck<'tcx> for PcgRef<'_, '_, 'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> std::result::Result<(), String> {
        self.capabilities.to_concrete(ctxt).check_validity(ctxt)?;
        self.borrow.check_validity(ctxt)?;
        self.owned
            .check_validity(&self.capabilities.to_concrete(ctxt), ctxt)?;
        if *CHECK_CYCLES && !self.is_acyclic(ctxt) {
            return Err("PCG is not acyclic".to_string());
        }

        for (place, cap) in self.capabilities.to_concrete(ctxt).iter() {
            if !self.owned.contains_place(place, ctxt)
                && !self.borrow.graph.places(ctxt).contains(&place)
            {
                return Err(format!(
                    "Place {} has capability {:?} but is not in the owned PCG or borrow graph",
                    place.to_short_string(ctxt),
                    cap
                ));
            }
        }

        // For now we don't do this, due to interactions with future nodes: we
        // detect that a node is no longer blocked but still technically not a
        // leaf due to historical reborrows that could have changed the value in
        // its lifetime projections see format_fields in tracing-subscriber
        //
        // In the future we might want to change how this works
        //
        // let leaf_places = self.leaf_places(ctxt);
        // for place in self.places(ctxt) {
        //     if self.capabilities.get(place, ctxt) == Some(CapabilityKind::Exclusive)
        //         && !leaf_places.contains(&place)
        //     {
        //         return Err(format!(
        //             "Place {} has exclusive capability but is not a leaf place",
        //             place.to_short_string(ctxt)
        //         ));
        //     }
        // }

        for edge in self.borrow.graph.edges() {
            match edge.kind {
                BorrowPcgEdgeKind::Deref(deref_edge) => {
                    if let MaybeLabelledPlace::Current(blocked_place) = deref_edge.blocked_place
                        && let MaybeLabelledPlace::Current(deref_place) = deref_edge.deref_place
                        && let Some(c @ (CapabilityKind::Read | CapabilityKind::Exclusive)) = self
                            .capabilities
                            .get(blocked_place, ctxt)
                            .map(|c| c.expect_concrete())
                        && self.capabilities.get(deref_place, ctxt).is_none()
                    {
                        return Err(format!(
                            "Deref edge {} blocked place {} has capability {:?} but deref place {} has no capability",
                            deref_edge.to_short_string(ctxt),
                            blocked_place.to_short_string(ctxt),
                            c,
                            deref_place.to_short_string(ctxt)
                        ));
                    }
                }
                BorrowPcgEdgeKind::Borrow(BorrowEdge::Local(borrow_edge)) => {
                    if let MaybeLabelledPlace::Current(blocked_place) = borrow_edge.blocked_place
                        && blocked_place.is_owned(ctxt)
                        && !self.owned.contains_place(blocked_place, ctxt)
                    {
                        return Err(format!(
                            "Borrow edge {} blocks owned place {}, which is not in the owned PCG",
                            borrow_edge.to_short_string(ctxt),
                            blocked_place.to_short_string(ctxt)
                        ));
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a> Pcg<'a, 'tcx> {
    pub(crate) fn is_expansion_leaf(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool {
        if self
            .borrow
            .graph()
            .edges_blocking(place.into(), ctxt)
            .any(|e| matches!(e.kind, BorrowPcgEdgeKind::BorrowPcgExpansion(_)))
        {
            return false;
        }

        return !place.is_owned(ctxt) || self.owned.leaf_places(ctxt).contains(&place);
    }

    pub fn capabilities(&self) -> &SymbolicPlaceCapabilities<'a, 'tcx> {
        &self.capabilities
    }

    pub fn owned_pcg(&self) -> &OwnedPcg<'tcx> {
        &self.owned
    }

    pub fn borrow_pcg(&self) -> &BorrowsState<'tcx> {
        &self.borrow
    }

    pub(crate) fn ensure_triple(&mut self, t: Triple<'tcx>, ctxt: AnalysisCtxt<'a, 'tcx>) {
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
        body_analysis: &BodyAnalysis<'a, 'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> std::result::Result<bool, PcgError> {
        let mut other_capabilities = other.capabilities.clone();
        let mut other_borrows = other.borrow.clone();
        let mut self_owned_data = JoinOwnedData {
            owned: &mut self.owned,
            borrows: &mut self.borrow,
            capabilities: &mut self.capabilities,
            block: self_block,
        };
        let other_owned_data = JoinOwnedData {
            owned: &other.owned,
            borrows: &mut other_borrows,
            capabilities: &mut other_capabilities,
            block: other_block,
        };
        let mut res = self_owned_data.join(other_owned_data, ctxt)?;
        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let mut other = other.clone();
        other
            .borrow
            .add_cfg_edge(other_block, self_block, ctxt.ctxt);
        res |= self.capabilities.join(&other_capabilities, ctxt);
        let borrow_args = JoinBorrowsArgs {
            self_block,
            other_block,
            body_analysis,
            capabilities: &mut self.capabilities,
            owned: &mut self.owned,
        };
        res |= self.borrow.join(&other.borrow, borrow_args, ctxt)?;
        Ok(res)
    }

    pub(crate) fn debug_lines(&self, repacker: CompilerCtxt<'a, 'tcx>) -> Vec<String> {
        let mut result = self.borrow.debug_lines(repacker);
        result.sort();
        let mut capabilities = self.capabilities.debug_lines(repacker);
        capabilities.sort();
        result.extend(capabilities);
        result
    }
    pub(crate) fn initialize_as_start_block(&mut self, analysis_ctxt: AnalysisCtxt<'a, 'tcx>) {
        self.owned
            .initialize_as_start_block(&mut self.capabilities, analysis_ctxt);
        self.borrow
            .initialize_as_start_block(&mut self.capabilities, analysis_ctxt);
    }
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
            PcgDomain::InProgress(d) => write!(f, "InProgressDomain({:?})", d.ctxt.block),
            PcgDomain::Complete(_d) => write!(f, "CompleteDomain"),
        }
    }
}

#[derive(From, Clone)]
pub enum PcgDomain<'a, 'tcx> {
    InProgress(InProgressDomain<'a, 'tcx>),
    Complete(CompleteDomain<'a, 'tcx>),
}

impl<'a, 'tcx> PcgDomain<'a, 'tcx> {
    pub(crate) fn expect_complete(&self) -> &CompleteDomain<'a, 'tcx> {
        match self {
            PcgDomain::Complete(d) => d,
            PcgDomain::InProgress(_d) => panic!("Expected complete domain, got in progress"),
        }
    }
}

mod private {
    use std::rc::Rc;

    use crate::{
        pcg::{
            BodyAnalysis, PcgDebugData, PcgDomainData, PcgError, ctxt::AnalysisCtxt,
            place_capabilities::SymbolicPlaceCapabilities,
        },
        utils::CompilerCtxt,
    };

    #[derive(Clone)]
    pub struct InProgressDomain<'a, 'tcx> {
        pub(crate) ctxt: AnalysisCtxt<'a, 'tcx>,
        pub(crate) body_analysis: Rc<BodyAnalysis<'a, 'tcx>>,
        pub(crate) data: std::result::Result<PcgDomainData<'a, 'tcx>, PcgError>,
        pub(crate) debug_data: Option<PcgDebugData>,
        pub(crate) reachable: bool,
    }

    #[derive(Clone)]
    pub struct CompleteDomain<'a, 'tcx> {
        pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
        pub(crate) data: std::result::Result<
            PcgDomainData<'a, 'tcx, SymbolicPlaceCapabilities<'a, 'tcx>>,
            PcgError,
        >,
    }
}

pub(crate) use private::*;

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

    pub fn pcg(&self, phase: impl Into<DomainDataIndex>) -> &Pcg<'a, 'tcx> {
        match &self.data {
            Ok(data) => &data.pcg[phase.into()],
            Err(e) => panic!("PCG error: {e:?}"),
        }
    }

    pub(crate) fn error(&self) -> Option<&PcgError> {
        self.data.as_ref().err()
    }

    pub(crate) fn data(&self) -> std::result::Result<&PcgDomainData<'_, 'tcx>, PcgError> {
        self.data.as_ref().map_err(|e| e.clone())
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

    pub(crate) fn new(
        body_analysis: Rc<BodyAnalysis<'a, 'tcx>>,
        debug_data: Option<PcgDebugData>,
        arena: PcgArena<'a>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Self {
        Self {
            ctxt,
            body_analysis,
            data: Ok(PcgDomainData::new(arena)),
            debug_data,
            reachable: false,
        }
    }

    pub(crate) fn generate_dot_graph(&self, phase: DataflowStmtPhase, statement_index: usize) {
        let pcg: &Pcg<'a, 'tcx> = match phase {
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
}

impl<'a, 'tcx> CompleteDomain<'a, 'tcx> {
    pub(crate) fn new(
        ctxt: CompilerCtxt<'a, 'tcx>,
        data: PcgDomainData<'a, 'tcx, SymbolicPlaceCapabilities<'a, 'tcx>>,
    ) -> Self {
        Self {
            ctxt,
            data: Ok(data),
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
    pub(crate) fn has_error(&self) -> bool {
        match self {
            PcgDomain::Complete(d) => d.data.is_err(),
            PcgDomain::InProgress(d) => d.data.is_err(),
        }
    }
    pub(crate) fn expect_in_progress(&self) -> &InProgressDomain<'a, 'tcx> {
        match self {
            PcgDomain::InProgress(d) => d,
            PcgDomain::Complete(_d) => panic!("Expected in progress domain, got complete"),
        }
    }
    pub(crate) fn expect_in_progress_mut(&mut self) -> &mut InProgressDomain<'a, 'tcx> {
        match self {
            PcgDomain::InProgress(d) => d,
            PcgDomain::Complete(_d) => panic!("Expected in progress domain, got complete"),
        }
    }
}

impl PcgDomain<'_, '_> {}

impl Eq for PcgDomain<'_, '_> {}

impl PartialEq for PcgDomain<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PcgDomain::Complete(d1), PcgDomain::Complete(d2)) => d1.data == d2.data,
            (PcgDomain::InProgress(d1), PcgDomain::InProgress(d2)) => d1.data == d2.data,
            _ => false,
        }
    }
}

impl JoinSemiLattice for PcgDomain<'_, '_> {
    // TODO: It should be possible to simplify this logic considerably because
    // each block should only be visited once.
    fn join(&mut self, other: &Self) -> bool {
        let slf = self.expect_in_progress_mut();
        let other = other.expect_in_progress();
        if !slf.reachable && !other.reachable {
            return false;
        }
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

        let is_loop_head = slf.body_analysis.is_loop_head(self_block);

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
            &slf.body_analysis,
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
            slf.generate_dot_graph(DataflowStmtPhase::Join(other.block()), 0);
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
