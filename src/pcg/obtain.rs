use std::marker::PhantomData;

use crate::{
    action::{BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_checker::r#impl::get_reserve_location,
    borrow_pcg::{
        action::LabelPlaceReason,
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike, LocalNode},
        borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion},
        edge::{
            deref::DerefEdge,
            kind::BorrowPcgEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
        edge_data::LabelPlacePredicate,
        graph::BorrowsGraph,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate, LabelNodeContext,
            LabelPlaceWithContext, SetLabel,
        },
        path_condition::ValidityConditions,
        region_projection::{LifetimeProjection, LocalLifetimeProjection},
        state::BorrowStateMutRef,
    },
    error::PcgError,
    r#loop::PlaceUsageType,
    owned_pcg::{ExpandedPlace, LocalExpansions, RepackCollapse, RepackOp},
    pcg::{
        CapabilityKind, PCGNodeLike, PcgMutRef, PcgRefLike,
        ctxt::AnalysisCtxt,
        place_capabilities::{
            BlockType, PlaceCapabilitiesInterface, PlaceCapabilitiesReader,
            SymbolicPlaceCapabilities,
        },
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DataflowCtxt, DebugImgcat, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace,
        Place, ProjectionKind, ShallowExpansion, SnapshotLocation, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
};

pub(crate) struct PlaceObtainer<'state, 'a, 'tcx, Ctxt = AnalysisCtxt<'a, 'tcx>> {
    pub(crate) pcg: PcgMutRef<'state, 'tcx>,
    pub(crate) ctxt: Ctxt,
    pub(crate) actions: Option<&'state mut Vec<PcgAction<'tcx>>>,
    pub(crate) location: mir::Location,
    pub(crate) prev_snapshot_location: SnapshotLocation,
    pub(crate) _marker: PhantomData<&'a ()>,
}

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> RenderDebugGraph
    for PlaceObtainer<'_, 'a, 'tcx, Ctxt>
{
    fn render_debug_graph(&self, debug_imgcat: Option<DebugImgcat>, comment: &str) {
        self.pcg.as_ref().render_debug_graph(
            self.location(),
            debug_imgcat,
            comment,
            self.ctxt.bc_ctxt(),
        );
    }
}

impl<Ctxt> HasSnapshotLocation for PlaceObtainer<'_, '_, '_, Ctxt> {
    fn prev_snapshot_location(&self) -> SnapshotLocation {
        self.prev_snapshot_location
    }
}

impl<'state, 'tcx, Ctxt> PlaceObtainer<'state, '_, 'tcx, Ctxt> {
    pub(crate) fn location(&self) -> mir::Location {
        self.location
    }

    pub(crate) fn new(
        pcg: PcgMutRef<'state, 'tcx>,
        actions: Option<&'state mut Vec<PcgAction<'tcx>>>,
        ctxt: Ctxt,
        location: mir::Location,
        prev_snapshot_location: SnapshotLocation,
    ) -> Self {
        Self {
            pcg,
            ctxt,
            actions,
            location,
            prev_snapshot_location,
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ObtainType {
    Capability(CapabilityKind),
    TwoPhaseExpand,
    LoopInvariant {
        is_blocked: bool,
        usage_type: PlaceUsageType,
    },
}

impl ObtainType {
    /// The capability to use when generating expand annotations.
    ///
    /// If we are intend to write to the place, an expansion must come
    /// from a place with exclusive permission, so we expand for that capability.
    /// A weaken will come later.
    pub(crate) fn capability_for_expand<'a, 'tcx>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> CapabilityKind
    where
        'tcx: 'a,
    {
        match self {
            ObtainType::Capability(CapabilityKind::Write) => CapabilityKind::Exclusive,
            _ => self.capability(place, ctxt),
        }
    }
    pub(crate) fn capability<'a, 'tcx>(
        self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> CapabilityKind
    where
        'tcx: 'a,
    {
        match self {
            ObtainType::Capability(cap) => cap,
            ObtainType::TwoPhaseExpand => CapabilityKind::Read,
            ObtainType::LoopInvariant {
                is_blocked: _,
                usage_type,
            } => {
                if usage_type == PlaceUsageType::Read
                    || place.is_shared_ref(ctxt)
                    || place.projects_shared_ref(ctxt)
                {
                    CapabilityKind::Read
                } else {
                    CapabilityKind::Exclusive
                }
            }
        }
    }

    pub(crate) fn should_label_rp<'a, 'tcx>(
        &self,
        rp: LifetimeProjection<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        match self {
            ObtainType::Capability(cap) => !cap.is_read(),
            ObtainType::TwoPhaseExpand => true,
            ObtainType::LoopInvariant { .. } => rp.base.is_mutable(ctxt),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum LabelForLifetimeProjection {
    NewLabelAtCurrentLocation(SnapshotLocation),
    ExistingLabelOfTwoPhaseReservation(SnapshotLocation),
    NoLabel,
}

use LabelForLifetimeProjection::*;
impl LabelForLifetimeProjection {
    fn label(self) -> Option<SnapshotLocation> {
        match self {
            NewLabelAtCurrentLocation(label) | ExistingLabelOfTwoPhaseReservation(label) => {
                Some(label)
            }
            NoLabel => None,
        }
    }
}

// TODO: The edges that are added here could just be part of the collapse "action" probably
pub(crate) trait PlaceCollapser<'a, 'tcx: 'a>:
    HasSnapshotLocation + ActionApplier<'tcx>
{
    fn get_local_expansions(&self, local: mir::Local) -> &LocalExpansions<'tcx>;

    fn borrows_state(&mut self) -> BorrowStateMutRef<'_, 'tcx>;

    fn capabilities(&mut self) -> &mut SymbolicPlaceCapabilities<'tcx>;

    fn leaf_places(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>>;

    fn restore_capability_to_leaf_places(
        &mut self,
        parent_place: Option<Place<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let mut leaf_places = self.leaf_places(ctxt.bc_ctxt());
        tracing::debug!(
            "Leaf places: {}",
            leaf_places.to_short_string(ctxt.bc_ctxt())
        );
        leaf_places.retain(|p| {
            self.capabilities().get(*p, ctxt) == Some(CapabilityKind::Read.into())
                && !p.projects_shared_ref(ctxt)
                && p.parent_place()
                    .is_none_or(|parent| self.capabilities().get(parent, ctxt).is_none())
        });
        tracing::debug!(
            "Restoring capability to leaf places: {}",
            leaf_places.to_short_string(ctxt.bc_ctxt())
        );
        for place in leaf_places {
            if let Some(parent_place) = parent_place {
                if !parent_place.is_prefix_of(place) {
                    continue;
                }
            }
            let action = PcgAction::restore_capability(
                place,
                CapabilityKind::Exclusive,
                "restore capability to leaf place",
                ctxt,
            );
            self.apply_action(action)?;
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, place, ctxt))]
    fn label_and_remove_capabilities_for_deref_projections_of_postfix_places(
        &mut self,
        place: Place<'tcx>,
        shared_refs_only: bool,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<bool, PcgError> {
        let place_predicate = |p| {
            if !place.is_strict_prefix_of(p) {
                return false;
            }
            if shared_refs_only {
                p.is_shared_ref(ctxt)
            } else {
                p.is_ref(ctxt)
            }
        };
        let derefs_to_disconnect = self
            .borrows_state()
            .graph
            .edges()
            .flat_map(|e| match e.kind() {
                BorrowPcgEdgeKind::Deref(e)
                    if let Some(p) = e.blocked_place.as_current_place()
                        && place_predicate(p) =>
                {
                    Some(*e)
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        for mut rp in derefs_to_disconnect.iter().copied() {
            tracing::info!(
                "Disconnecting deref projection {}",
                rp.to_short_string(ctxt.bc_ctxt())
            );
            let conditions = self.borrows_state().graph.remove(&rp.into()).unwrap();
            let label = self.prev_snapshot_location();
            rp.blocked_place.label_place_with_context(
                &LabelPlacePredicate::Exact(rp.blocked_place.place()),
                &SetLabel(label),
                LabelNodeContext::Other,
                ctxt.bc_ctxt(),
            );
            self.capabilities()
                .remove_all_postfixes(rp.deref_place.as_current_place().unwrap(), ctxt);
            rp.deref_place.label_place_with_context(
                &LabelPlacePredicate::Exact(rp.deref_place.place()),
                &SetLabel(self.prev_snapshot_location()),
                LabelNodeContext::TargetOfExpansion,
                ctxt.bc_ctxt(),
            );
            self.apply_action(
                BorrowPcgAction::add_edge(
                    BorrowPcgEdge::new(rp.into(), conditions.clone()),
                    format!(
                        "label_deref_projections_of_postfix_places. Shared refs only: {}",
                        shared_refs_only
                    ),
                    ctxt,
                )
                .into(),
            )?;
        }
        // TODO: THis could be a hack
        if !derefs_to_disconnect.is_empty() {
            tracing::info!(
                "Labeling deref projections for place {}",
                place.to_short_string(ctxt.ctxt())
            );
            self.apply_action(
                BorrowPcgAction::label_place_and_update_related_capabilities(
                    place,
                    self.prev_snapshot_location(),
                    LabelPlaceReason::LabelDerefProjections { shared_refs_only },
                )
                .into(),
            )?;
        }
        Ok(true)
    }

    /// Collapses owned places and performs appropriate updates to lifetime projections.
    fn collapse_owned_places_and_lifetime_projections_to(
        &mut self,
        place: Place<'tcx>,
        capability: CapabilityKind,
        context: String,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let to_collapse = self
            .get_local_expansions(place.local)
            .places_to_collapse_for_obtain_of(place, ctxt);
        tracing::debug!(
            "To obtain {}, will collapse {}",
            place.to_short_string(ctxt.ctxt()),
            to_collapse.to_short_string(ctxt.ctxt())
        );
        for place in to_collapse {
            let expansions = self
                .get_local_expansions(place.local)
                .expansions_from(place)
                .cloned()
                .collect::<Vec<_>>();
            self.apply_action(PcgAction::Owned(OwnedPcgAction::new(
                RepackOp::Collapse(RepackCollapse::new(place, capability)),
                Some(context.clone()),
            )))?;
            for pe in expansions {
                for rp in place.lifetime_projections(ctxt) {
                    let rp_expansion: Vec<LocalLifetimeProjection<'tcx>> = place
                        .expansion_places(&pe.expansion, ctxt)
                        .unwrap()
                        .into_iter()
                        .flat_map(|ep| {
                            ep.lifetime_projections(ctxt)
                                .into_iter()
                                .filter(|erp| erp.region(ctxt) == rp.region(ctxt))
                                .map(|erp| erp.into())
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    if rp_expansion.len() > 1 && capability.is_exclusive() {
                        self.create_aggregate_lifetime_projections(rp.into(), &rp_expansion, ctxt)?;
                    }
                }
            }
        }

        Ok(())
    }

    /// Only for owned places.
    fn create_aggregate_lifetime_projections(
        &mut self,
        base: LocalLifetimeProjection<'tcx>,
        expansion: &[LocalLifetimeProjection<'tcx>],
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        for (idx, node) in expansion.iter().enumerate() {
            if let Some(place) = node.base.as_current_place() {
                let labeller = SetLabel(self.prev_snapshot_location());
                self.borrows_state().graph.label_place(
                    (*place).into(),
                    LabelPlaceReason::Collapse,
                    &labeller,
                    ctxt,
                );
                let mut node = *node;
                node.label_place_with_context(
                    &LabelPlacePredicate::Exact((*place).into()),
                    &labeller,
                    LabelNodeContext::Other,
                    ctxt.bc_ctxt(),
                );
                let edge = BorrowPcgEdge::new(
                    BorrowFlowEdge::new(
                        node.into(),
                        base,
                        BorrowFlowEdgeKind::Aggregate {
                            field_idx: idx,
                            target_rp_index: 0, // TODO
                        },
                        ctxt,
                    )
                    .into(),
                    self.borrows_state().validity_conditions.clone(),
                );
                self.apply_action(
                    BorrowPcgAction::add_edge(edge, "create_aggregate_lifetime_projections", ctxt)
                        .into(),
                )?;
            }
        }
        Ok(())
    }
}

pub(crate) trait ActionApplier<'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError>;
}

pub(crate) trait HasSnapshotLocation {
    /// The snapshot location to use when e.g. moving out a place. Before
    /// performing such an action on a place, we would first update references
    /// to the place to use the version that is *labelled* with the location
    /// returned by this function (indicating that it refers to the value in the
    /// place before the action).
    fn prev_snapshot_location(&self) -> SnapshotLocation;
}

pub(crate) trait RenderDebugGraph {
    fn render_debug_graph(&self, debug_imgcat: Option<DebugImgcat>, comment: &str);
}

pub(crate) trait PlaceExpander<'a, 'tcx: 'a>:
    HasSnapshotLocation + ActionApplier<'tcx> + RenderDebugGraph
{
    fn contains_owned_expansion_to(&self, target: Place<'tcx>) -> bool;

    fn update_capabilities_for_borrow_expansion(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
        block_type: BlockType,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError>;

    fn update_capabilities_for_deref(
        &mut self,
        ref_place: Place<'tcx>,
        capability: CapabilityKind,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError>;

    #[tracing::instrument(skip(self, obtain_type, ctxt))]
    fn expand_to(
        &mut self,
        place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        for (base, _) in place.iter_projections(ctxt.ctxt()) {
            let base = base.with_inherent_region(ctxt);
            let expansion = base.expand_one_level(place, ctxt)?;
            if self.expand_place_one_level(base, &expansion, obtain_type, ctxt)? {
                tracing::debug!(
                    "expand region projections for {} one level",
                    base.to_short_string(ctxt.ctxt())
                );
                self.expand_lifetime_projections_one_level(base, &expansion, obtain_type, ctxt)?;
            }
        }
        Ok(())
    }

    fn label_for_rp(
        &self,
        rp: LifetimeProjection<'tcx, Place<'tcx>>,
        obtain_type: ObtainType,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> LabelForLifetimeProjection {
        use LabelForLifetimeProjection::*;
        if obtain_type.should_label_rp(rp.rebase(), ctxt) {
            NewLabelAtCurrentLocation(self.prev_snapshot_location())
        } else {
            match self.label_for_shared_expansion_of_rp(rp, ctxt) {
                Some(label) => ExistingLabelOfTwoPhaseReservation(label),
                None => NoLabel,
            }
        }
    }

    /// If the base of `rp` is blocked by a two-phase borrow, we want to use the
    /// existing label of its expansion
    fn label_for_shared_expansion_of_rp(
        &self,
        rp: LifetimeProjection<'tcx, Place<'tcx>>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Option<SnapshotLocation> {
        ctxt.bc()
            .borrows_blocking(rp.base, self.location(), ctxt.bc_ctxt())
            .first()
            .map(|borrow| {
                let borrow_reserve_location = get_reserve_location(borrow);
                SnapshotLocation::after_statement_at(borrow_reserve_location, ctxt)
            })
    }

    fn expand_owned_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<bool, PcgError> {
        if self.contains_owned_expansion_to(expansion.target_place) {
            tracing::debug!(
                "Already contains owned expansion from {}",
                base.to_short_string(ctxt.ctxt())
            );
            return Ok(false);
        }
        tracing::debug!(
            "New owned expansion from {}",
            base.to_short_string(ctxt.ctxt())
        );
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
                    Some(format!("Expand owned place one level ({:?})", obtain_type)),
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
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<bool, PcgError> {
        let place_expansion = PlaceExpansion::from_places(expansion.expansion(), ctxt);
        if matches!(expansion.kind, ProjectionKind::DerefRef(_)) {
            if self
                .borrows_graph()
                .contains_deref_edge_to(base.project_deref(ctxt))
            {
                return Ok(false);
            }
            let blocked_lifetime_projection_label = if base.is_mut_ref(ctxt) {
                Some(self.prev_snapshot_location())
            } else {
                self.label_for_shared_expansion_of_rp(
                    base.base_lifetime_projection(ctxt).unwrap(),
                    ctxt,
                )
            };
            let deref = DerefEdge::new(base, blocked_lifetime_projection_label, ctxt);
            self.render_debug_graph(None, "expand_place_one_level: before apply action");
            let action = BorrowPcgAction::add_edge(
                BorrowPcgEdge::new(deref.into(), self.path_conditions()),
                "expand_place_one_level: add deref edge",
                ctxt,
            );
            self.apply_action(action.into())?;
            self.render_debug_graph(None, "expand_place_one_level: after apply action");
            self.update_capabilities_for_deref(
                base,
                obtain_type.capability(base, ctxt),
                ctxt.bc_ctxt(),
            )?;
            self.render_debug_graph(
                None,
                "expand_place_one_level: after update_capabilities_for_deref",
            );
            if deref.blocked_lifetime_projection.label().is_some() {
                self.apply_action(
                    BorrowPcgAction::label_lifetime_projection(
                        LabelLifetimeProjectionPredicate::Equals(
                            deref.blocked_lifetime_projection.with_label(None, ctxt),
                        ),
                        deref.blocked_lifetime_projection.label(),
                        "block deref",
                    )
                    .into(),
                )?;
            }
            Ok(true)
        } else if base.is_owned(ctxt) {
            self.expand_owned_place_one_level(base, expansion, obtain_type, ctxt)
        } else {
            self.add_borrow_pcg_expansion(base, place_expansion, obtain_type, ctxt)
        }
    }

    fn location(&self) -> mir::Location;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx>;

    fn path_conditions(&self) -> ValidityConditions;

    fn add_borrow_pcg_expansion(
        &mut self,
        base: Place<'tcx>,
        place_expansion: PlaceExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<bool, PcgError>
    where
        'tcx: 'a,
    {
        let expanded_place = ExpandedPlace {
            place: base,
            expansion: place_expansion,
        };
        if self
            .borrows_graph()
            .contains_borrow_pcg_expansion(&expanded_place, ctxt)?
        {
            return Ok(false);
        }
        tracing::debug!(
            "Create expansion from {}",
            base.to_short_string(ctxt.bc_ctxt())
        );
        let block_type = expanded_place.expansion.block_type(base, obtain_type, ctxt);
        tracing::debug!(
            "Block type for {} is {:?}",
            base.to_short_string(ctxt.bc_ctxt()),
            block_type
        );
        let expansion: BorrowPcgExpansion<'tcx, LocalNode<'tcx>> =
            BorrowPcgExpansion::new(base.into(), expanded_place.expansion, ctxt)?;

        self.render_debug_graph(
            None,
            &format!(
                "add_borrow_pcg_expansion: before update_capabilities_for_borrow_expansion {}",
                expansion.to_short_string(ctxt.bc_ctxt())
            ),
        );
        self.update_capabilities_for_borrow_expansion(&expansion, block_type, ctxt.bc_ctxt())?;
        self.render_debug_graph(
            None,
            "add_borrow_pcg_expansion: after update_capabilities_for_borrow_expansion",
        );
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
    fn expand_lifetime_projections_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        for base_rp in base.lifetime_projections(ctxt) {
            if let Some(place_expansion) =
                expansion.place_expansion_for_region(base_rp.region(ctxt), ctxt)
            {
                tracing::debug!("Expand {}", base_rp.to_short_string(ctxt.bc_ctxt()));
                let mut expansion = BorrowPcgExpansion::new(base_rp.into(), place_expansion, ctxt)?;
                let expansion_label = self.label_for_rp(base_rp, obtain_type, ctxt);
                if let Some(label) = expansion_label.label() {
                    expansion.label_lifetime_projection(
                        &LabelLifetimeProjectionPredicate::Equals(base_rp.into()),
                        Some(label.into()),
                        ctxt.bc_ctxt(),
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
                        BorrowPcgAction::label_lifetime_projection(
                            LabelLifetimeProjectionPredicate::Equals(base_rp.into()),
                            Some(label.into()),
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
                                node.to_pcg_node(ctxt.bc_ctxt())
                                    .try_into_region_projection()
                                    .unwrap()
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
        origin_rp: LocalLifetimeProjection<'tcx>,
        expansion_rps: &[LifetimeProjection<'tcx>],
        context: &str,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
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
        old_source: LocalLifetimeProjection<'tcx>,
        new_source: LocalLifetimeProjection<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
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
