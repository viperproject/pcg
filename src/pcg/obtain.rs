use crate::{
    action::{BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_checker::r#impl::get_reserve_location,
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike, LocalNode},
        borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion},
        edge::{
            kind::BorrowPcgEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
        edge_data::LabelPlacePredicate,
        graph::BorrowsGraph,
        has_pcs_elem::{
            LabelPlace, LabelRegionProjection, LabelRegionProjectionPredicate, SetLabel,
        },
        path_condition::PathConditions,
        region_projection::{self, LocalRegionProjection, RegionProjection, RegionProjectionLabel},
    },
    free_pcs::{CapabilityKind, RepackOp},
    pcg::{
        obtain, place_capabilities::BlockType, EvalStmtPhase, PCGNodeLike, Pcg, PcgDebugData,
        PcgError, PcgMutRef,
    },
    rustc_interface::middle::mir,
    utils::{
        callbacks::in_cargo_crate, display::DisplayWithCompilerCtxt, maybe_old::MaybeOldPlace,
        CompilerCtxt, HasPlace, Place, ProjectionKind, ShallowExpansion, SnapshotLocation,
    },
};

pub(crate) struct PlaceObtainer<'state, 'mir, 'tcx> {
    pub(crate) pcg: PcgMutRef<'state, 'tcx>,
    pub(crate) phase: EvalStmtPhase,
    pub(crate) ctxt: CompilerCtxt<'mir, 'tcx>,
    pub(crate) actions: Option<&'state mut Vec<PcgAction<'tcx>>>,
    pub(crate) location: mir::Location,
    pub(crate) snapshot_location: SnapshotLocation,
    pub(crate) debug_data: Option<&'state mut PcgDebugData>,
}

impl<'state, 'mir, 'tcx> PlaceObtainer<'state, 'mir, 'tcx> {
    pub(crate) fn location(&self) -> mir::Location {
        self.location
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ObtainType {
    Capability(CapabilityKind),
    TwoPhaseExpand,
    LoopInvariant,
}

impl ObtainType {
    pub(crate) fn capability<'tcx>(
        &self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> CapabilityKind {
        match self {
            ObtainType::Capability(cap) => *cap,
            ObtainType::TwoPhaseExpand => CapabilityKind::Read,
            ObtainType::LoopInvariant => {
                if place.is_shared_ref(ctxt) || place.projects_shared_ref(ctxt) {
                    CapabilityKind::Read
                } else {
                    CapabilityKind::Exclusive
                }
            }
        }
    }

    pub(crate) fn should_label_rp<'tcx>(
        &self,
        rp: RegionProjection<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            ObtainType::Capability(cap) => !cap.is_read(),
            ObtainType::TwoPhaseExpand => true,
            ObtainType::LoopInvariant => rp.base.is_mutable(ctxt),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum LabelForRegionProjection {
    NewLabelAtCurrentLocation(RegionProjectionLabel),
    ExistingLabelOfTwoPhaseReservation(RegionProjectionLabel),
    NoLabel,
}

use LabelForRegionProjection::*;
impl LabelForRegionProjection {
    fn label(self) -> Option<RegionProjectionLabel> {
        match self {
            NewLabelAtCurrentLocation(label) | ExistingLabelOfTwoPhaseReservation(label) => {
                Some(label)
            }
            NoLabel => None,
        }
    }
    fn apply<'tcx>(
        self,
        rp: RegionProjection<'tcx, Place<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> RegionProjection<'tcx, Place<'tcx>> {
        rp.with_label(self.label(), ctxt)
    }
}

pub(crate) trait PlaceExpander<'mir, 'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError>;

    fn contains_owned_expansion_from(&self, base: Place<'tcx>) -> bool;

    fn update_capabilities_for_borrow_expansion(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
        block_type: BlockType,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError>;

    fn expand_to(
        &mut self,
        place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError> {
        for (base, _) in place.iter_projections(ctxt) {
            let base = base.with_inherent_region(ctxt);
            let expansion = base.expand_one_level(place, ctxt)?;
            if self.expand_place_one_level(base, &expansion, obtain_type, ctxt)? {
                tracing::debug!(
                    "expand region projections for {} one level",
                    base.to_short_string(ctxt)
                );
                self.expand_region_projections_one_level(base, &expansion, obtain_type, ctxt)?;
            }
        }
        Ok(())
    }

    fn label_for_rp(
        &self,
        rp: RegionProjection<'tcx, Place<'tcx>>,
        obtain_type: ObtainType,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> LabelForRegionProjection {
        use LabelForRegionProjection::*;
        if obtain_type.should_label_rp(rp.rebase(), ctxt) {
            NewLabelAtCurrentLocation(self.current_snapshot_location().into())
        } else {
            match self.label_for_shared_expansion_of_rp(rp, ctxt) {
                Some(label) => ExistingLabelOfTwoPhaseReservation(label),
                None => NoLabel,
            }
        }
    }

    fn label_for_shared_expansion_of_rp(
        &self,
        rp: RegionProjection<'tcx, Place<'tcx>>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Option<RegionProjectionLabel> {
        for borrow in
            ctxt.bc
                .borrows_blocking(rp.base, self.current_snapshot_location().location(), ctxt)
        {
            return Some(SnapshotLocation::Mid(get_reserve_location(&borrow)).into());
        }
        None
    }

    fn expand_owned_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: crate::utils::CompilerCtxt<'mir, 'tcx>,
    ) -> Result<bool, PcgError> {
        if self.contains_owned_expansion_from(base) {
            tracing::debug!(
                "Already contains owned expansion from {}",
                base.to_short_string(ctxt)
            );
            return Ok(false);
        }
        tracing::debug!("New owned expansion from {}", base.to_short_string(ctxt));
        if expansion.kind.is_deref_box()
            && obtain_type.capability(base, ctxt).is_shallow_exclusive()
        {
            self.apply_action(
                OwnedPcgAction::new(
                    RepackOp::DerefShallowInit(expansion.base_place(), expansion.target_place),
                    None,
                )
                .into(),
            )?;
        } else {
            self.apply_action(
                OwnedPcgAction::new(
                    RepackOp::expand(
                        expansion.base_place(),
                        expansion.guide(),
                        obtain_type.capability(expansion.base_place(), ctxt),
                        ctxt,
                    ),
                    None,
                )
                .into(),
            )?;
        }
        Ok(true)
    }

    fn expand_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<bool, PcgError> {
        let place_expansion = PlaceExpansion::from_places(expansion.expansion(), ctxt);
        let expansion_is_owned = base.is_owned(ctxt)
            && !matches!(
                expansion.kind,
                ProjectionKind::DerefRef(_) | ProjectionKind::DerefRawPtr(_)
            );
        if expansion_is_owned {
            self.expand_owned_place_one_level(base, expansion, obtain_type, ctxt)
        } else {
            self.add_borrow_pcg_expansion(base, place_expansion, obtain_type, ctxt)
        }
    }

    fn current_snapshot_location(&self) -> SnapshotLocation;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx>;

    fn path_conditions(&self) -> PathConditions;

    fn add_borrow_pcg_expansion(
        &mut self,
        base: Place<'tcx>,
        place_expansion: PlaceExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<bool, PcgError> {
        if self
            .borrows_graph()
            .contains_borrow_pcg_expansion_of(base, &place_expansion, ctxt)
        {
            return Ok(false);
        }
        tracing::debug!("Create expansion from {}", base.to_short_string(ctxt));
        let expansion_label = if base.is_ref(ctxt) {
            Some(self.label_for_rp(
                base.base_region_projection(ctxt).unwrap(),
                obtain_type,
                ctxt,
            ))
        } else {
            None
        };
        let block_type = place_expansion.block_type(base, obtain_type, ctxt);
        let expansion: BorrowPcgExpansion<'tcx, LocalNode<'tcx>> = BorrowPcgExpansion::new(
            base.into(),
            place_expansion,
            expansion_label.and_then(|lbl| lbl.label()),
            ctxt,
        )?;

        if let Some(NewLabelAtCurrentLocation(location)) = expansion_label {
            let rp = base.base_region_projection(ctxt).unwrap();
            self.apply_action(
                BorrowPcgAction::label_region_projection(
                    LabelRegionProjectionPredicate::Equals(rp.into()),
                    Some(location),
                    "add_borrow_pcg_expansion: fresh RP label",
                )
                .into(),
            )?;
        }

        self.update_capabilities_for_borrow_expansion(&expansion, block_type, ctxt)?;
        let action = BorrowPcgAction::add_edge(
            BorrowPcgEdge::new(
                BorrowPcgEdgeKind::BorrowPcgExpansion(expansion),
                self.path_conditions(),
            ),
            "add_borrow_pcg_expansion",
            ctxt,
        );
        self.apply_action(action.into())?;
        Ok(true)
    }

    #[tracing::instrument(skip(self, base, expansion, ctxt))]
    fn expand_region_projections_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError> {
        for base_rp in base.region_projections(ctxt) {
            if let Some(place_expansion) =
                expansion.place_expansion_for_region(base_rp.region(ctxt), ctxt)
            {
                tracing::debug!("Expand {}", base_rp.to_short_string(ctxt));
                let mut expansion =
                    BorrowPcgExpansion::new(base_rp.into(), place_expansion, None, ctxt)?;
                let expansion_label = self.label_for_rp(base_rp, obtain_type, ctxt);
                if let Some(label) = expansion_label.label() {
                    expansion.label_region_projection(
                        &LabelRegionProjectionPredicate::Equals(base_rp.into()),
                        Some(label),
                        ctxt,
                    );
                }
                self.apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion.clone()),
                            self.path_conditions(),
                        ),
                        "expand_region_projections_one_level",
                        ctxt,
                    )
                    .into(),
                )?;
                if let NewLabelAtCurrentLocation(label) = expansion_label {
                    self.apply_action(
                        BorrowPcgAction::label_region_projection(
                            LabelRegionProjectionPredicate::Equals(base_rp.into()),
                            Some(label),
                            "expand_region_projections_one_level: create new RP label",
                        )
                        .into(),
                    )?;

                    // Don't add placeholder edges for owned expansions, unless its a deref
                    if !base.is_owned(ctxt) || base.is_mut_ref(ctxt) {
                        let old_rp_base = base_rp.with_label(Some(label.into()), ctxt);
                        let expansion_rps = expansion
                            .expansion()
                            .iter()
                            .map(|node| {
                                node.to_pcg_node(ctxt).try_into_region_projection().unwrap()
                            })
                            .collect::<Vec<_>>();
                        self.add_and_update_placeholder_edges(
                            old_rp_base.into(),
                            &expansion_rps,
                            "obtain",
                            ctxt,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    // This is used when labelling an interior RP
    // This will label and add edges to the outer one.
    // So we'd turn eg :
    // {s|'a} -> {s.f|'a at X} -> {q|'a} -> {s.f|'a at Future}
    //                  ^                         ^
    //                  |-------------------------|
    // into:
    // {s|'a at X} -> {s.f|'a at X} -> {q|'a} -> {s.f|'a at Future} -> {s|'a at Future}
    //        ^         ^                         ^                          ^
    //        |         |-------------------------|                          |
    //        |                                                              |
    //        |--------------------------------------------------------------|                                                             ^
    fn add_future_edges_and_mutate_current_rp_expansion(
        &mut self,
        edge: BorrowPcgExpansion<'tcx>,
        context: &str,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError> {
        let base_rp = edge.base.try_into_region_projection().unwrap();
        assert!(base_rp.label().is_none());
        let expansion_rps = edge
            .expansion()
            .iter()
            .map(|node| node.to_pcg_node(ctxt).try_into_region_projection().unwrap())
            .collect::<Vec<_>>();
        self.add_and_update_placeholder_edges(base_rp, &expansion_rps, context, ctxt)?;
        Ok(())
    }

    // In general the origin_rp should already be labelled
    fn add_and_update_placeholder_edges(
        &mut self,
        origin_rp: LocalRegionProjection<'tcx>,
        expansion_rps: &[RegionProjection<'tcx>],
        context: &str,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError> {
        if expansion_rps.is_empty() {
            return Ok(());
        }
        let future_rp = origin_rp.with_placeholder_label(ctxt);

        // Add edge {origin|r'a at l} -> {origin|r'a at FUTURE}
        self.apply_action(
            BorrowPcgAction::add_edge(
                BorrowPcgEdge::new(
                    BorrowFlowEdge::new(
                        origin_rp.into(),
                        future_rp,
                        BorrowFlowEdgeKind::Future,
                        ctxt,
                    )
                    .into(),
                    self.path_conditions(),
                ),
                format!("{}: placeholder bookkeeping", context),
                ctxt,
            )
            .into(),
        )?;

        // For each field F add edge {origin.F|'a} -> {origin|r'a at FUTURE}
        for expansion_rp in expansion_rps {
            self.apply_action(
                BorrowPcgAction::add_edge(
                    BorrowPcgEdge::new(
                        BorrowFlowEdge::new(
                            *expansion_rp,
                            future_rp,
                            BorrowFlowEdgeKind::Future,
                            ctxt,
                        )
                        .into(),
                        self.path_conditions(),
                    ),
                    format!("{}: placeholder bookkeeping", context),
                    ctxt,
                )
                .into(),
            )?;
        }

        // For all borrowflow edges blocking {origin|r'a at l} (except the one to origin|r'a at FUTURE)
        // They should now be blocking the future one instead
        let to_replace = self
            .borrows_graph()
            .edges_blocking(origin_rp.into(), ctxt)
            .filter_map(|edge| {
                if let BorrowPcgEdgeKind::BorrowFlow(bf_edge) = edge.kind {
                    if bf_edge.kind == BorrowFlowEdgeKind::Future && bf_edge.short() != future_rp {
                        return Some((
                            edge.to_owned_edge(),
                            BorrowPcgEdge::new(
                                BorrowFlowEdge::new(
                                    future_rp.into(),
                                    bf_edge.short(),
                                    BorrowFlowEdgeKind::Future,
                                    ctxt,
                                )
                                .into(),
                                edge.conditions.clone(),
                            ),
                        ));
                    }
                }
                None
            })
            .collect::<Vec<_>>();
        for (to_remove, to_insert) in to_replace {
            self.apply_action(
                BorrowPcgAction::remove_edge(to_remove, "placeholder bookkeeping").into(),
            )?;
            self.apply_action(
                BorrowPcgAction::add_edge(to_insert, "placeholder bookkeeping", ctxt).into(),
            )?;
        }
        Ok(())
    }
}
