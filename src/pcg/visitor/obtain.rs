use std::cmp::Ordering;

use itertools::Itertools;

use crate::action::{BorrowPcgAction, OwnedPcgAction};
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, LocalNode};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::free_pcs::{CapabilityKind, RepackOp};
use crate::pcg::PCGNodeLike;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::ShallowExpansion;

use crate::utils::place::HasPlace;
use crate::utils::{Place, ProjectionKind, SnapshotLocation};

use super::{PcgError, PcgVisitor};
impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn upgrade_read_to_exclusive(&mut self, place: Place<'tcx>) -> Result<(), PcgError> {
        self.record_and_apply_action(
            BorrowPcgAction::restore_capability(
                place,
                CapabilityKind::Exclusive,
                "upgrade_read_to_exclusive",
            )
            .into(),
        )?;
        if let Some(parent) = place.parent_place() {
            self.remove_read_permission_upwards(parent)?;
        }
        Ok(())
    }

    pub(crate) fn remove_read_permission_upwards(
        &mut self,
        mut current: Place<'tcx>,
    ) -> Result<(), PcgError> {
        while self.pcg.capabilities.get(current) == Some(CapabilityKind::Read) {
            self.record_and_apply_action(
                BorrowPcgAction::weaken(current, CapabilityKind::Read, None).into(),
            )?;
            let parent = match current.parent_place() {
                Some(parent) => parent,
                None => break,
            };
            current = parent;
        }
        Ok(())
    }

    pub(crate) fn upgrade_closest_root_to_exclusive(
        &mut self,
        place: Place<'tcx>,
    ) -> Result<(), PcgError> {
        let mut expand_root = place;
        loop {
            if let Some(cap) = self.pcg.capabilities.get(expand_root) {
                if cap.is_read() {
                    self.upgrade_read_to_exclusive(expand_root)?;
                }
                return Ok(());
            }
            if let Some(parent) = expand_root.parent_place() {
                expand_root = parent;
            } else {
                return Ok(());
            }
        }
    }

    fn place_to_collapse_to(&self, place: Place<'tcx>) -> Place<'tcx> {
        let mut current = place;
        let capability_projs = self.pcg.owned.locals()[place.local].get_allocated();
        loop {
            if self.pcg.capabilities.get(current).is_some() {
                return current;
            }
            if capability_projs.contains_expansion_to(current, self.ctxt) {
                return current;
            }
            current = current.parent_place().unwrap();
        }
    }

    fn add_deref_expansion(
        &mut self,
        base: Place<'tcx>,
        place_expansion: PlaceExpansion<'tcx>,
        obtain_type: ObtainType,
    ) -> Result<bool, PcgError> {
        let expansion: BorrowPcgExpansion<'tcx, LocalNode<'tcx>> = BorrowPcgExpansion::new(
            base.into(),
            place_expansion,
            if base.is_mut_ref(self.ctxt) && obtain_type.should_label_rp() {
                Some(self.current_snapshot_location().into())
            } else {
                None
            },
            self.ctxt,
        )?;

        tracing::debug!(
            "Adding edge {} (label rp: {})",
            expansion.to_short_string(self.ctxt),
            obtain_type.should_label_rp()
        );

        if expansion
            .blocked_by_nodes(self.ctxt)
            .all(|node| self.pcg.borrow.graph().contains(node, self.ctxt))
        {
            return Ok(false);
        }

        if base.is_mut_ref(self.ctxt) && obtain_type.should_label_rp() {
            let place: MaybeOldPlace<'tcx> = base.into();
            let rp = place.base_region_projection(self.ctxt).unwrap();
            tracing::debug!(
                "Labeling {} with {:?}",
                rp.to_short_string(self.ctxt),
                self.location
            );
            self.record_and_apply_action(
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
                self.pcg.borrow.path_conditions.clone(),
            ),
            "add_deref_expansion",
            obtain_type.capability().is_read(),
        );
        self.record_and_apply_action(action.into())
    }

    fn expand_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
    ) -> Result<bool, PcgError> {
        let place_expansion = PlaceExpansion::from_places(expansion.expansion(), self.ctxt);
        let expansion_is_owned = base.is_owned(self.ctxt)
            && !matches!(
                expansion.kind,
                ProjectionKind::DerefRef(_) | ProjectionKind::DerefRawPtr(_)
            );
        if expansion_is_owned {
            let capability_projs = self.pcg.owned.locals_mut()[base.local].get_allocated_mut();
            if capability_projs.contains_expansion_from(base) {
                return Ok(false);
            } else if expansion.kind.is_box() && obtain_type.capability().is_shallow_exclusive() {
                self.record_and_apply_action(
                    OwnedPcgAction::new(
                        RepackOp::DerefShallowInit(expansion.base_place(), expansion.target_place),
                        None,
                    )
                    .into(),
                )?;
            } else {
                self.record_and_apply_action(
                    OwnedPcgAction::new(
                        RepackOp::expand(
                            expansion.base_place(),
                            expansion.guide(),
                            obtain_type.capability(),
                            self.ctxt,
                        ),
                        None,
                    )
                    .into(),
                )?;
            }
        } else {
            self.add_deref_expansion(base, place_expansion, obtain_type)?;
        }
        Ok(true)
    }

    pub(crate) fn current_snapshot_location(&self) -> SnapshotLocation {
        if self.phase.is_operands_stage() {
            SnapshotLocation::before(self.location)
        } else {
            SnapshotLocation::Mid(self.location)
        }
    }

    fn expand_region_projections_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
    ) -> Result<(), PcgError> {
        for rp in base.region_projections(self.ctxt) {
            if let Some(place_expansion) =
                expansion.place_expansion_for_region(rp.region(self.ctxt), self.ctxt)
            {
                let rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>> = rp.into();
                let expansion =
                    BorrowPcgExpansion::new(rp.into(), place_expansion, None, self.ctxt)?;
                tracing::debug!("Adding edge {}", expansion.to_short_string(self.ctxt));
                self.record_and_apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion.clone()),
                            self.pcg.borrow.path_conditions.clone(),
                        ),
                        "expand_region_projections_one_level",
                        obtain_type.capability().is_read(),
                    )
                    .into(),
                )?;
                if rp.base.is_current()
                    && rp.can_be_labelled(self.ctxt)
                    && obtain_type.should_label_rp()
                {
                    tracing::debug!("Expand and label {}", rp.to_short_string(self.ctxt));
                    let label = self.current_snapshot_location();
                    self.record_and_apply_action(
                        BorrowPcgAction::label_region_projection(
                            rp,
                            Some(label.into()),
                            "expand_region_projections_one_level",
                        )
                        .into(),
                    )?;

                    // Don't add placeholder edges for owned expansions, unless its a deref
                    if !base.is_owned(self.ctxt) || base.is_mut_ref(self.ctxt) {
                        let old_rp_base = rp.with_label(Some(label.into()), self.ctxt);
                        let expansion_rps = expansion
                            .expansion()
                            .iter()
                            .map(|node| {
                                node.to_pcg_node(self.ctxt)
                                    .try_into_region_projection()
                                    .unwrap()
                            })
                            .collect::<Vec<_>>();
                        self.add_and_update_placeholder_edges(
                            old_rp_base,
                            &expansion_rps,
                            "obtain",
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    fn expand_to(&mut self, place: Place<'tcx>, obtain_type: ObtainType) -> Result<(), PcgError> {
        for (base, _) in place.iter_projections(self.ctxt) {
            let base = base.with_inherent_region(self.ctxt);
            let expansion = base.expand_one_level(place, self.ctxt)?;
            if self.expand_place_one_level(base, &expansion, obtain_type)? {
                self.expand_region_projections_one_level(base, &expansion, obtain_type)?;
            }
        }
        Ok(())
    }

    pub(crate) fn collapse(
        &mut self,
        place: Place<'tcx>,
        capability: CapabilityKind,
        context: String,
    ) -> Result<(), PcgError> {
        let capability_projs = self.pcg.owned.locals_mut()[place.local].get_allocated_mut();
        let expansions = capability_projs
            .expansions
            .iter()
            .filter(|(p, _)| place.is_prefix(**p))
            .map(|(p, e)| (*p, e.clone()))
            .sorted_by_key(|(p, _)| p.projection.len())
            .rev()
            .collect::<Vec<_>>();
        for (p, expansion) in expansions {
            self.record_and_apply_action(
                OwnedPcgAction::new(
                    RepackOp::collapse(p, expansion.guide(), capability),
                    Some(context.clone()),
                )
                .into(),
            )?;
            for rp in p.region_projections(self.ctxt) {
                let rp_expansion: Vec<LocalNode<'tcx>> = p
                    .expansion_places(&expansion, self.ctxt)
                    .into_iter()
                    .flat_map(|ep| {
                        ep.region_projections(self.ctxt)
                            .into_iter()
                            .filter(|erp| erp.region(self.ctxt) == rp.region(self.ctxt))
                            .map(|erp| erp.into())
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                if rp_expansion.len() > 1 {
                    self.redirect_blocked_nodes_to_base(rp.into(), &rp_expansion)?;
                }
            }
        }
        Ok(())
    }

    /// Ensures that the place is expanded to the given place, with a certain
    /// capability.
    ///
    /// This also handles corresponding region projections of the place.
    pub(crate) fn obtain(
        &mut self,
        place: Place<'tcx>,
        obtain_type: ObtainType,
    ) -> Result<(), PcgError> {
        if !obtain_type.capability().is_read() {
            self.upgrade_closest_root_to_exclusive(place)?;
        }

        let current_cap = self.pcg.capabilities.get(place);

        if current_cap.is_none()
            || matches!(
                current_cap.unwrap().partial_cmp(&obtain_type.capability()),
                Some(Ordering::Less) | None
            )
        {
            let collapse_to = self.place_to_collapse_to(place);
            self.collapse(
                collapse_to,
                obtain_type.capability(),
                format!("Obtain {}", place.to_short_string(self.ctxt)),
            )?;
        }

        // if obtain_type.capability().is_write() {
        //     let _ = self.record_and_apply_action(
        //         BorrowPcgAction::make_place_old(place, MakePlaceOldReason::ReAssign).into(),
        //     );
        // }

        self.expand_to(place, obtain_type)?;

        // pcg_validity_assert!(
        //     self.pcg.capabilities.get(place.into()).is_some(),
        //     "{:?}: Place {:?} does not have a capability after obtain {:?}",
        //     location,
        //     place,
        //     capability
        // );
        // pcg_validity_assert!(
        //     self.pcg.capabilities.get(place.into()).unwrap() >= capability,
        //     "{:?} Capability {:?} for {:?} is not greater than {:?}",
        //     location,
        //     self.pcg.capabilities.get(place.into()).unwrap(),
        //     place,
        //     capability
        // );
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ObtainType {
    Capability(CapabilityKind),
    TwoPhaseExpand,
}

impl ObtainType {
    fn capability(&self) -> CapabilityKind {
        match self {
            ObtainType::Capability(cap) => *cap,
            ObtainType::TwoPhaseExpand => CapabilityKind::Read,
        }
    }

    fn should_label_rp(&self) -> bool {
        match self {
            ObtainType::Capability(cap) => !cap.is_read(),
            ObtainType::TwoPhaseExpand => true,
        }
    }
}
