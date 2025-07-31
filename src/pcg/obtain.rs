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
        graph::BorrowsGraph,
        has_pcs_elem::{LabelRegionProjection, LabelRegionProjectionPredicate},
        path_condition::ValidityConditions,
        region_projection::{LocalRegionProjection, RegionProjection, RegionProjectionLabel},
    },
    free_pcs::{CapabilityKind, RepackOp},
    pcg::{PCGNodeLike, PcgDebugData, PcgError, PcgMutRef, place_capabilities::BlockType},
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, HasPlace, Place, ProjectionKind, ShallowExpansion, SnapshotLocation,
        display::DisplayWithCompilerCtxt,
    },
};

pub(crate) struct PlaceObtainer<'state, 'mir, 'tcx> {
    pub(crate) pcg: PcgMutRef<'state, 'tcx>,
    pub(crate) ctxt: CompilerCtxt<'mir, 'tcx>,
    pub(crate) actions: Option<&'state mut Vec<PcgAction<'tcx>>>,
    pub(crate) location: mir::Location,
    pub(crate) prev_snapshot_location: SnapshotLocation,
    pub(crate) debug_data: Option<&'state mut PcgDebugData>,
}

impl PlaceObtainer<'_, '_, '_> {
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
    /// The capability to use when generating expand annotations.
    ///
    /// If we are intend to write to the place, an expansion must come
    /// from a place with exclusive permission, so we expand for that capability.
    /// A weaken will come later.
    pub(crate) fn capability_for_expand<'tcx>(
        &self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> CapabilityKind {
        match self {
            ObtainType::Capability(CapabilityKind::Write) => CapabilityKind::Exclusive,
            _ => self.capability(place, ctxt),
        }
    }
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

    #[tracing::instrument(skip(self, obtain_type, ctxt))]
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
            NewLabelAtCurrentLocation(self.prev_snapshot_location().into())
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
        ctxt.bc
            .borrows_blocking(rp.base, self.location(), ctxt)
            .first()
            .map(|borrow| {
                let borrow_reserve_location = get_reserve_location(borrow);
                let snapshot_location =
                    SnapshotLocation::after_statement_at(borrow_reserve_location, ctxt);
                snapshot_location.into()
            })
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
                        obtain_type.capability_for_expand(expansion.base_place(), ctxt),
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

    fn prev_snapshot_location(&self) -> SnapshotLocation;

    fn location(&self) -> mir::Location;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx>;

    fn path_conditions(&self) -> ValidityConditions;

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
        tracing::debug!(
            "Block type for {} is {:?}",
            base.to_short_string(ctxt),
            block_type
        );
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
                        let old_rp_base = base_rp.with_label(Some(label), ctxt);
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

    /// Performs bookkeeping for future nodes in the case where capability from
    /// (generally lablled) `origin_rp` is is temporarily transferred to
    /// (unlablled) `expansion_rps`, but will eventually be transferred back to
    /// `origin_rp`.
    ///
    /// This happens in the case of borrows and expansions of borrowed places,
    /// in which case `origin_rp` is labelled.
    /// We also use this for constructing loop abstractions where `origin_rp`
    /// is unlabelled (the labels are added in a later stage).
    ///
    /// The logic as as follows:
    ///
    /// Adds a node `future_rp` which is the future node for `origin_rp`.
    ///
    /// 1. Add a Future edge from `origin_rp` to `future_rp`
    /// 2. Add Future edges from each `expansion_rp` to `future_rp`
    /// 3. All Future edges with source `origin_rp` (except for the one
    ///    created in step 1) are modified to now have source `future_rp`
    ///
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
        self.redirect_source_of_future_edges(origin_rp, future_rp, ctxt)?;
        Ok(())
    }

    fn redirect_source_of_future_edges(
        &mut self,
        old_source: LocalRegionProjection<'tcx>,
        new_source: LocalRegionProjection<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError> {
        let to_replace = self
            .borrows_graph()
            .edges_blocking(old_source.into(), ctxt)
            .filter_map(|edge| {
                if let BorrowPcgEdgeKind::BorrowFlow(bf_edge) = edge.kind {
                    if bf_edge.kind == BorrowFlowEdgeKind::Future && bf_edge.short() != new_source {
                        return Some((
                            edge.to_owned_edge(),
                            BorrowPcgEdge::new(
                                BorrowFlowEdge::new(
                                    new_source.into(),
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
