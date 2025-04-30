use std::cmp::Ordering;

use itertools::Itertools;

use crate::borrow_pcg::borrow_pcg_edge::{BorrowPCGEdge, LocalNode};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::free_pcs::{CapabilityKind, RepackOp};
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::Location;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::{borrow_pcg::action::BorrowPCGAction, utils::ShallowExpansion};

use crate::utils::place::HasPlace;
use crate::utils::{Place, ProjectionKind, SnapshotLocation};

use super::{PcgError, PcgVisitor};
impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn upgrade_read_to_exclusive(&mut self, place: Place<'tcx>) -> Result<(), PcgError> {
        self.record_and_apply_action(
            BorrowPCGAction::restore_capability(place.into(), CapabilityKind::Exclusive).into(),
        )?;
        self.remove_read_permission_upwards(place)?;
        Ok(())
    }

    pub(crate) fn remove_read_permission_upwards(
        &mut self,
        mut current: Place<'tcx>,
    ) -> Result<(), PcgError> {
        while !current.is_owned(self.ctxt)
            && self.pcg.capabilities.get(current.into()) == Some(CapabilityKind::Read)
        {
            self.record_and_apply_action(
                BorrowPCGAction::weaken(current, CapabilityKind::Read, None).into(),
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
            if let Some(cap) = self.pcg.capabilities.get(expand_root.into()) {
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
            if self.pcg.capabilities.get(current.into()).is_some() {
                return current;
            }
            if capability_projs.contains_expansion_to(current, self.ctxt) {
                return current;
            }
            current = current.parent_place().unwrap();
        }
    }

    fn expand_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &ShallowExpansion<'tcx>,
        location: Location,
        capability: CapabilityKind,
    ) -> Result<bool, PcgError> {
        let place_expansion = PlaceExpansion::from_places(expansion.expansion().clone(), self.ctxt);
        let expansion_is_owned = base.is_owned(self.ctxt)
            && !matches!(
                expansion.kind,
                ProjectionKind::DerefRef(_) | ProjectionKind::DerefRawPtr(_)
            );
        if expansion_is_owned {
            let capability_projs = self.pcg.owned.locals_mut()[base.local].get_allocated_mut();
            if capability_projs.contains_expansion_from(base) {
                return Ok(false);
            } else {
                if expansion.kind.is_box() && capability.is_shallow_exclusive() {
                    self.record_and_apply_action(
                        RepackOp::DerefShallowInit(expansion.base_place(), expansion.target_place)
                            .into(),
                    )?;
                } else {
                    self.record_and_apply_action(
                        RepackOp::Expand(
                            expansion.base_place(),
                            expansion.target_place,
                            capability,
                        )
                        .into(),
                    )?;
                }
            }
        } else {
            let expansion: BorrowPcgExpansion<'tcx, LocalNode<'tcx>> = BorrowPcgExpansion::new(
                base.into(),
                place_expansion,
                location,
                capability != CapabilityKind::Read,
                self.ctxt,
            )?;

            if expansion
                .blocked_by_nodes(self.ctxt)
                .iter()
                .all(|node| self.pcg.borrow.graph().contains(*node, self.ctxt))
            {
                return Ok(false);
            }

            if base.is_mut_ref(self.ctxt)
                && base.contains_mutable_region_projections(self.ctxt)
                && capability != CapabilityKind::Read
            {
                let place: MaybeOldPlace<'tcx> = base.into();
                self.pcg.borrow.label_region_projection(
                    &place.base_region_projection(self.ctxt).unwrap(),
                    Some(location.into()),
                    self.ctxt,
                );
            }

            let action = BorrowPCGAction::add_edge(
                BorrowPCGEdge::new(
                    BorrowPcgEdgeKind::BorrowPcgExpansion(expansion),
                    PathConditions::new(location.block),
                ),
                capability != CapabilityKind::Read,
            );
            self.record_and_apply_action(action.into())?;
        }
        Ok(true)
    }

    fn expand_to(
        &mut self,
        place: Place<'tcx>,
        location: Location,
        capability: CapabilityKind,
    ) -> Result<(), PcgError> {
        for (base, _) in place.iter_projections(self.ctxt) {
            let base = base.with_inherent_region(self.ctxt);
            let expansion = base.expand_one_level(place, self.ctxt)?;
            let for_exclusive = capability != CapabilityKind::Read;
            if self.expand_place_one_level(base, &expansion, location, capability)? {
                for rp in base.region_projections(self.ctxt) {
                    let dest_places = expansion
                        .expansion()
                        .iter()
                        .filter(|e| {
                            e.region_projections(self.ctxt)
                                .into_iter()
                                .any(|child_rp| rp.region(self.ctxt) == child_rp.region(self.ctxt))
                        })
                        .copied()
                        .collect::<Vec<_>>();
                    if !dest_places.is_empty() {
                        let rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>> = rp.into();
                        let place_expansion = PlaceExpansion::from_places(dest_places, self.ctxt);
                        let expansion = BorrowPcgExpansion::new(
                            rp.into(),
                            place_expansion,
                            location,
                            for_exclusive,
                            self.ctxt,
                        )?;
                        self.record_and_apply_action(
                            BorrowPCGAction::add_edge(
                                BorrowPCGEdge::new(
                                    BorrowPcgEdgeKind::BorrowPcgExpansion(expansion),
                                    PathConditions::new(location.block),
                                ),
                                for_exclusive,
                            )
                            .into(),
                        )?;
                        if base.is_mut_ref(self.ctxt) && for_exclusive {
                            self.pcg.borrow.label_region_projection(
                                &rp,
                                Some(SnapshotLocation::before(location).into()),
                                self.ctxt,
                            );
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn collapse(&mut self, place: Place<'tcx>, capability: CapabilityKind) -> Result<(), PcgError> {
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
                RepackOp::Collapse(p, p.expansion_places(&expansion, self.ctxt)[0], capability)
                    .into(),
            )?;
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
        location: Location,
        capability: CapabilityKind,
    ) -> Result<(), PcgError> {
        if capability != CapabilityKind::Read {
            self.upgrade_closest_root_to_exclusive(place)?;
        }

        let current_cap = self.pcg.capabilities.get(place.into());

        if current_cap.is_none()
            || matches!(
                current_cap.unwrap().partial_cmp(&capability),
                Some(Ordering::Less) | None
            )
        {
            let collapse_to = self.place_to_collapse_to(place);
            self.collapse(collapse_to, capability)?;
        }

        self.expand_to(place, location, capability)?;

        // The place holds a borrow, that is derefed in the borrow PCG.
        // Therefore, it has either no capability or read capability. It will
        // soon be labelled in the borrow PCG, meaning the (current) place will
        // imminently become a a leaf at which point it would in principle have
        // the capability anyways
        if place.is_owned(self.ctxt)
            && self.pcg.borrow.graph().contains(place, self.ctxt)
            && capability.is_write()
        {
            self.pcg.capabilities.insert(place.into(), capability);
        }

        pcg_validity_assert!(
            self.pcg.capabilities.get(place.into()).is_some(),
            "{:?}: Place {:?} does not have a capability after obtain {:?}",
            location,
            place,
            capability
        );
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
