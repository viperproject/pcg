use crate::{
    DebugLines,
    borrow_pcg::{
        edge::{borrow::BorrowEdge, kind::BorrowPcgEdgeKind},
        graph::{BorrowsGraph, join::JoinBorrowsArgs},
        state::{BorrowStateMutRef, BorrowStateRef, BorrowsState, BorrowsStateLike},
    },
    borrows_imgcat_debug,
    error::PcgError,
    owned_pcg::{OwnedPcg, join::data::JoinOwnedData},
    pcg::{
        CapabilityKind,
        ctxt::AnalysisCtxt,
        place_capabilities::{
            PlaceCapabilities, PlaceCapabilitiesReader, SymbolicPlaceCapabilities,
        },
        triple::Triple,
    },
    rustc_interface::middle::mir,
    utils::{
        CHECK_CYCLES, CompilerCtxt, DebugImgcat, HasBorrowCheckerCtxt, Place,
        data_structures::HashSet, display::DisplayWithCompilerCtxt, maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
    visualization::{dot_graph::DotGraph, generate_pcg_dot_graph},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pcg<'tcx, Capabilities = SymbolicPlaceCapabilities<'tcx>> {
    pub(crate) owned: OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowsState<'tcx>,
    pub(crate) capabilities: Capabilities,
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
    pub(crate) capabilities: &'pcg SymbolicPlaceCapabilities<'tcx>,
}

impl<'tcx> PcgRef<'_, 'tcx> {
    pub(crate) fn render_debug_graph<'slf, 'a>(
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
    pub(crate) capabilities: &'pcg mut SymbolicPlaceCapabilities<'tcx>,
}

impl<'pcg, 'tcx> PcgMutRef<'pcg, 'tcx> {
    pub(crate) fn new(
        owned: &'pcg mut OwnedPcg<'tcx>,
        borrow: BorrowStateMutRef<'pcg, 'tcx>,
        capabilities: &'pcg mut SymbolicPlaceCapabilities<'tcx>,
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

pub(crate) trait PcgRefLike<'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx>;

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

impl<'tcx> HasValidityCheck<'tcx> for PcgRef<'_, 'tcx> {
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

impl<'a, 'tcx: 'a> Pcg<'tcx> {
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

    pub fn places_with_capapability(&self, capability: CapabilityKind) -> HashSet<Place<'tcx>> {
        self.capabilities
            .iter()
            .filter_map(|(p, c)| {
                if c == capability.into() {
                    Some(p)
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn capabilities(&self) -> &SymbolicPlaceCapabilities<'tcx> {
        &self.capabilities
    }

    pub fn owned_pcg(&self) -> &OwnedPcg<'tcx> {
        &self.owned
    }

    pub fn borrow_pcg(&self) -> &BorrowsState<'tcx> {
        &self.borrow
    }

    pub(crate) fn ensure_triple<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        t: Triple<'tcx>,
        ctxt: Ctxt,
    ) {
        self.owned.ensures(t, &mut self.capabilities, ctxt);
    }

    #[tracing::instrument(skip(self, other, ctxt))]
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_block: mir::BasicBlock,
        other_block: mir::BasicBlock,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> std::result::Result<(), PcgError> {
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
        self_owned_data.join(other_owned_data, ctxt)?;
        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let mut other = other.clone();
        other
            .borrow
            .add_cfg_edge(other_block, self_block, ctxt.ctxt);
        self.capabilities.join(&other_capabilities, ctxt);
        let borrow_args = JoinBorrowsArgs {
            self_block,
            other_block,
            body_analysis: ctxt.body_analysis,
            capabilities: &mut self.capabilities,
            owned: &mut self.owned,
        };
        self.borrow.join(&other.borrow, borrow_args, ctxt)?;
        Ok(())
    }

    pub(crate) fn debug_lines(&self, repacker: CompilerCtxt<'a, 'tcx>) -> Vec<String> {
        let mut result = self.borrow.debug_lines(repacker);
        result.sort();
        let mut capabilities = self.capabilities.debug_lines(repacker);
        capabilities.sort();
        result.extend(capabilities);
        result
    }
    pub(crate) fn start_block(analysis_ctxt: AnalysisCtxt<'a, 'tcx>) -> Self {
        let mut capabilities = PlaceCapabilities::default();
        let owned = OwnedPcg::start_block(&mut capabilities, analysis_ctxt);
        let borrow = BorrowsState::start_block(&mut capabilities, analysis_ctxt);
        Pcg {
            owned,
            borrow,
            capabilities,
        }
    }
}
