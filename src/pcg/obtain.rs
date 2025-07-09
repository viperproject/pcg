use std::marker::PhantomData;

use crate::{
    action::{BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike, LocalNode},
        borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion},
        edge::{
            kind::BorrowPcgEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
        edge_data::EdgeData,
        graph::BorrowsGraph,
        path_condition::PathConditions,
        region_projection::{LocalRegionProjection, RegionProjection, RegionProjectionLabel},
    },
    free_pcs::{CapabilityKind, RepackOp},
    pcg::{PCGNodeLike, PcgError},
    pcg_validity_assert,
    utils::{
        maybe_old::MaybeOldPlace, CompilerCtxt, HasPlace, Place, ProjectionKind, ShallowExpansion,
        SnapshotLocation,
    },
};

#[derive(Debug, Clone, Copy)]
pub(crate) enum ObtainType {
    Capability(CapabilityKind),
    TwoPhaseExpand,
}

impl ObtainType {
    pub(crate) fn capability(&self) -> CapabilityKind {
        match self {
            ObtainType::Capability(cap) => *cap,
            ObtainType::TwoPhaseExpand => CapabilityKind::Read,
        }
    }

    pub(crate) fn should_label_rp(&self) -> bool {
        match self {
            ObtainType::Capability(cap) => !cap.is_read(),
            ObtainType::TwoPhaseExpand => true,
        }
    }
}

pub(crate) trait Expander<'mir, 'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError>;

    fn contains_owned_expansion_from(
        &self,
        base: Place<'tcx>,
    ) -> bool;

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
                self.expand_region_projections_one_level(base, &expansion, obtain_type, ctxt)?;
            }
        }
        Ok(())
    }

    fn expand_owned_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: crate::utils::CompilerCtxt<'mir, 'tcx>,
    ) -> Result<bool, PcgError> {
        if self.contains_owned_expansion_from(base) {
            return Ok(false);
        }
        if expansion.kind.is_box() && obtain_type.capability().is_shallow_exclusive() {
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
                        obtain_type.capability(),
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
            self.expand_owned_place_one_level(base, expansion, obtain_type, ctxt)?;
        } else {
            self.add_deref_expansion(base, place_expansion, obtain_type, ctxt)?;
        }
        Ok(true)
    }

    fn current_snapshot_location(&self) -> SnapshotLocation;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx>;

    fn path_conditions(&self) -> PathConditions;

    fn add_deref_expansion(
        &mut self,
        base: Place<'tcx>,
        place_expansion: PlaceExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<bool, PcgError> {
        let expansion: BorrowPcgExpansion<'tcx, LocalNode<'tcx>> = BorrowPcgExpansion::new(
            base.into(),
            place_expansion,
            if base.is_mut_ref(ctxt) && obtain_type.should_label_rp() {
                Some(self.current_snapshot_location().into())
            } else {
                None
            },
            ctxt,
        )?;

        if self
            .borrows_graph()
            .contains_deref_expansion_from(base, ctxt)
        {
            return Ok(false);
        }

        if base.is_mut_ref(ctxt) && obtain_type.should_label_rp() {
            let place: MaybeOldPlace<'tcx> = base.into();
            let rp = place.base_region_projection(ctxt).unwrap();
            self.apply_action(
                BorrowPcgAction::label_region_projection(
                    rp,
                    Some(self.current_snapshot_location().into()),
                    "add_deref_expansion",
                )
                .into(),
            )?;
        }

        let action = BorrowPcgAction::add_edge(
            BorrowPcgEdge::new(
                BorrowPcgEdgeKind::BorrowPcgExpansion(expansion),
                self.path_conditions(),
            ),
            "add_deref_expansion",
            obtain_type.capability().is_read(),
        );
        self.apply_action(action.into())
    }

    fn expand_region_projections_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError> {
        for rp in base.region_projections(ctxt) {
            if let Some(place_expansion) =
                expansion.place_expansion_for_region(rp.region(ctxt), ctxt)
            {
                let rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>> = rp.into();
                let expansion = BorrowPcgExpansion::new(rp.into(), place_expansion, None, ctxt)?;
                self.apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion.clone()),
                            self.path_conditions(),
                        ),
                        "expand_region_projections_one_level",
                        obtain_type.capability().is_read(),
                    )
                    .into(),
                )?;
                if rp.base.is_current() && rp.can_be_labelled(ctxt) && obtain_type.should_label_rp()
                {
                    let label = self.current_snapshot_location();
                    self.apply_action(
                        BorrowPcgAction::label_region_projection(
                            rp,
                            Some(label.into()),
                            "expand_region_projections_one_level",
                        )
                        .into(),
                    )?;

                    // Don't add placeholder edges for owned expansions, unless its a deref
                    if !base.is_owned(ctxt) || base.is_mut_ref(ctxt) {
                        let old_rp_base = rp.with_label(Some(label.into()), ctxt);
                        let expansion_rps = expansion
                            .expansion()
                            .iter()
                            .map(|node| {
                                node.to_pcg_node(ctxt).try_into_region_projection().unwrap()
                            })
                            .collect::<Vec<_>>();
                        self.add_and_update_placeholder_edges(
                            old_rp_base,
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
    fn add_and_update_placeholder_edges(
        &mut self,
        labelled_rp: LocalRegionProjection<'tcx>,
        expansion_rps: &[RegionProjection<'tcx>],
        context: &str,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError> {
        if expansion_rps.is_empty() {
            return Ok(());
        }
        let future_rp = labelled_rp.with_placeholder_label(ctxt);
        self.apply_action(
            BorrowPcgAction::add_edge(
                BorrowPcgEdge::new(
                    BorrowFlowEdge::new(
                        labelled_rp.into(),
                        future_rp,
                        BorrowFlowEdgeKind::Future,
                        ctxt,
                    )
                    .into(),
                    self.path_conditions(),
                ),
                format!("{}: placeholder bookkeeping", context),
                false,
            )
            .into(),
        )?;
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
                    false,
                )
                .into(),
            )?;
        }
        let to_replace = self
            .borrows_graph()
            .edges_blocking(labelled_rp.into(), ctxt)
            .into_iter()
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
                BorrowPcgAction::add_edge(to_insert, "placeholder bookkeeping", false).into(),
            )?;
        }
        Ok(())
    }
}
