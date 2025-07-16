use std::cmp::Ordering;

use itertools::Itertools;

use crate::action::{BorrowPcgAction, OwnedPcgAction};
use crate::borrow_pcg::action::MakePlaceOldReason;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::has_pcs_elem::LabelPlace;
use crate::borrow_pcg::region_projection::LocalRegionProjection;
use crate::free_pcs::{CapabilityKind, RepackOp};
use crate::pcg::obtain::{self, Expander, ObtainType};
use crate::pcg::place_capabilities::PlaceCapabilitiesInterface;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::{HasPlace, ShallowExpansion};

use crate::utils::{Place, SnapshotLocation};

use super::{PcgError, PcgVisitor};
impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn upgrade_read_to_exclusive(&mut self, place: Place<'tcx>) -> Result<(), PcgError> {
        tracing::debug!(
            "upgrade_read_to_exclusive: {}",
            place.to_short_string(self.ctxt)
        );
        self.record_and_apply_action(
            BorrowPcgAction::restore_capability(
                place,
                CapabilityKind::Exclusive,
                "upgrade_read_to_exclusive",
            )
            .into(),
        )?;
        self.remove_read_permission_downwards(place)?;
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
                BorrowPcgAction::weaken(
                    current,
                    CapabilityKind::Read,
                    None,
                    "Remove read permission upwards",
                    self.ctxt,
                )
                .into(),
            )?;
            let parent = match current.parent_place() {
                Some(parent) => parent,
                None => break,
            };
            current = parent;
        }
        Ok(())
    }

    pub(crate) fn remove_read_permission_downwards(
        &mut self,
        upgraded_place: Place<'tcx>,
    ) -> Result<(), PcgError> {
        let to_remove = self
            .pcg
            .capabilities
            .iter()
            .filter(|(p, _)| {
                p.projection.len() > upgraded_place.projection.len() && upgraded_place.is_prefix(*p)
            })
            .collect::<Vec<_>>();
        for (p, cap) in to_remove {
            self.record_and_apply_action(
                BorrowPcgAction::weaken(
                    p,
                    cap,
                    None,
                    "Remove read permission downwards",
                    self.ctxt,
                )
                .into(),
            )?;
        }
        Ok(())
    }

    pub(crate) fn upgrade_closest_root_to_exclusive(
        &mut self,
        place: Place<'tcx>,
    ) -> Result<(), PcgError> {
        tracing::debug!(
            "upgrade_closest_root_to_exclusive: {}",
            place.to_short_string(self.ctxt)
        );
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
                let rp_expansion: Vec<LocalRegionProjection<'tcx>> = p
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
                if rp_expansion.len() > 1 && capability.is_exclusive() {
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
            tracing::debug!(
                "Obtain {:?} to place {} in phase {:?}",
                obtain_type,
                place.to_short_string(self.ctxt),
                self.phase
            );
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

        if obtain_type.capability().is_write() {
            let _ = self.record_and_apply_action(
                BorrowPcgAction::make_place_old(place, MakePlaceOldReason::ReAssign).into(),
            );
        }

        self.expand_to(place, obtain_type, self.ctxt)?;

        if !matches!(obtain_type, ObtainType::Capability(CapabilityKind::Read)) {
            let deref_projections_of_postfix_places = self
                .pcg
                .borrow
                .graph
                .edges()
                .flat_map(|e| match e.kind() {
                    BorrowPcgEdgeKind::BorrowPcgExpansion(e)
                        if let Some(p) = e.deref_blocked_place(self.ctxt)
                            && place != p
                            && place.is_prefix(p) =>
                    {
                        Some(e.clone())
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();

            for mut rp in deref_projections_of_postfix_places {
                let conditions = self.pcg.borrow.graph.remove(&rp.clone().into()).unwrap();
                rp.base.label_place(
                    &LabelPlacePredicate::PrefixWithoutIndirectionOrPostfix(rp.base.place()),
                    &self.pcg.borrow.latest,
                    self.ctxt,
                );
                rp.expansion.iter_mut().for_each(|e| {
                    e.label_place(
                        &LabelPlacePredicate::PrefixWithoutIndirectionOrPostfix(e.place()),
                        &self.pcg.borrow.latest,
                        self.ctxt,
                    );
                });
                self.pcg
                    .borrow
                    .graph
                    .insert(BorrowPcgEdge::new(rp.into(), conditions), self.ctxt);
            }

            self.record_and_apply_action(
                BorrowPcgAction::make_place_old(
                    place,
                    MakePlaceOldReason::LabelPostfixesOfPlaceToObtain,
                )
                .into(),
            )?;
        }

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

impl<'mir, 'tcx> Expander<'mir, 'tcx> for PcgVisitor<'_, 'mir, 'tcx> {
    fn apply_action(&mut self, action: crate::action::PcgAction<'tcx>) -> Result<bool, PcgError> {
        self.record_and_apply_action(action)
    }

    fn contains_owned_expansion_from(&self, base: Place<'tcx>) -> bool {
        self.pcg.owned.locals()[base.local]
            .get_allocated()
            .contains_expansion_from(base)
    }

    fn expand_owned_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        obtain_type: ObtainType,
        _ctxt: crate::utils::CompilerCtxt<'mir, 'tcx>,
    ) -> Result<bool, PcgError> {
        if self.contains_owned_expansion_from(base) {
            return Ok(false);
        }
        if expansion.kind.is_box() && obtain_type.capability().is_shallow_exclusive() {
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
        Ok(true)
    }

    fn current_snapshot_location(&self) -> SnapshotLocation {
        if self.phase.is_operands_stage() {
            SnapshotLocation::before(self.location)
        } else {
            SnapshotLocation::Mid(self.location)
        }
    }

    fn borrows_graph(&self) -> &crate::borrow_pcg::graph::BorrowsGraph<'tcx> {
        &self.pcg.borrow.graph
    }

    fn path_conditions(&self) -> crate::borrow_pcg::path_condition::PathConditions {
        self.pcg.borrow.path_conditions.clone()
    }
}
