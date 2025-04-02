// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    borrow_pcg::state::BorrowsState,
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections, RepackOp},
    pcg::{place_capabilities::PlaceCapabilities, PcgError},
    pcg_validity_assert,
    rustc_interface::{
        ast::Mutability,
        middle::mir::{Local, RETURN_PLACE},
    },
    utils::{
        corrected::CorrectedPlace, display::DisplayWithRepacker, LocalMutationIsAllowed, Place,
        PlaceRepacker,
    },
};

use super::{
    triple::{Condition, Triple},
    CapabilityLocals,
};

impl<'tcx> CapabilityLocals<'tcx> {
    #[tracing::instrument(skip(self, cond, repacker, borrows))]
    pub(crate) fn requires(
        &mut self,
        cond: Condition<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
        borrows: &BorrowsState<'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        match cond {
            Condition::RemoveCapability(place) => {
                place_capabilities.remove(place.into());
                Ok(vec![])
            }
            Condition::Unalloc(_) => Ok(vec![]),
            Condition::AllocateOrDeallocate(local) => {
                match &mut self[local] {
                    cap @ CapabilityLocal::Unallocated => {
                        // A bit of an unusual case: we're at a StorageDead but
                        // already deallocated. Allocate now so that the
                        // precondition of SD can be met, but we'll catch this in
                        // `bridge` and emit a IgnoreSD op.
                        *cap = CapabilityLocal::Allocated(CapabilityProjections::new(local));
                        place_capabilities.insert(local.into(), CapabilityKind::Write);
                        Ok(vec![])
                    }
                    CapabilityLocal::Allocated(_) => self.requires(
                        Condition::Capability(local.into(), CapabilityKind::Write),
                        repacker,
                        place_capabilities,
                        borrows,
                    ),
                }
            }
            Condition::Capability(place, cap) => {
                let nearest_owned_place = place.nearest_owned_place(repacker);
                let cp = self[nearest_owned_place.local].get_allocated_mut();
                tracing::debug!("Repack to {nearest_owned_place:?} for {place:?} in {cp:?}");
                let result = cp.repack(place, place_capabilities, repacker, cap)?;
                if nearest_owned_place != place {
                    match nearest_owned_place.ref_mutability(repacker) {
                        Some(Mutability::Mut) => {
                            place_capabilities.remove(nearest_owned_place.into());
                        }
                        Some(Mutability::Not) => {
                            place_capabilities
                                .insert(nearest_owned_place.into(), CapabilityKind::Read);
                        }
                        None => unreachable!(),
                    }
                }
                Ok(result)
            }
            Condition::Return => {
                let always_live = repacker.always_live_locals();
                for local in 0..repacker.local_count() {
                    let local = Local::from_usize(local);
                    let pre = if local == RETURN_PLACE {
                        Condition::Capability(RETURN_PLACE.into(), CapabilityKind::Exclusive)
                    } else if always_live.contains(local) {
                        Condition::Capability(local.into(), CapabilityKind::Write)
                    } else {
                        Condition::Unalloc(local)
                    };
                    self.check_pre_satisfied(pre, place_capabilities, repacker);
                }
                Ok(vec![])
            }
        }
    }

    fn check_pre_satisfied(
        &self,
        pre: Condition<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        match pre {
            Condition::RemoveCapability(_place) => {}
            Condition::Unalloc(local) => {
                assert!(
                    self[local].is_unallocated(),
                    "local: {local:?}, fpcs: {self:?}\n"
                );
            }
            Condition::AllocateOrDeallocate(_local) => {
            }
            Condition::Capability(place, cap) => {
                match cap {
                    CapabilityKind::Read => {
                        // TODO
                    }
                    CapabilityKind::Write => {
                        // Cannot get write on a shared ref
                        pcg_validity_assert!(place
                            .is_mutable(LocalMutationIsAllowed::Yes, repacker)
                            .is_ok());
                    }
                    CapabilityKind::Exclusive => {
                        // Cannot get exclusive on a shared ref
                        assert!(
                            !place.projects_shared_ref(repacker),
                            "Cannot get exclusive on projection of shared ref {}",
                            place.to_short_string(repacker)
                        );
                    }
                    CapabilityKind::ShallowExclusive => unreachable!(),
                }

                let _cp = self[place.local].get_allocated();
                // assert_eq!(cp[&place], *cap); // TODO: is this too strong for shallow exclusive?
            }
            Condition::Return => {
                let always_live = repacker.always_live_locals();
                for local in 0..repacker.local_count() {
                    let local = Local::from_usize(local);
                    let pre = if local == RETURN_PLACE {
                        Condition::Capability(RETURN_PLACE.into(), CapabilityKind::Exclusive)
                    } else if always_live.contains(local) {
                        Condition::Capability(local.into(), CapabilityKind::Write)
                    } else {
                        Condition::Unalloc(local)
                    };
                    self.check_pre_satisfied(pre, capabilities, repacker);
                }
            }
        }
    }
    pub(crate) fn ensures(
        &mut self,
        t: Triple<'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.check_pre_satisfied(t.pre(), place_capabilities, repacker);
        let Some(post) = t.post() else {
            return;
        };
        match post {
            Condition::Return => unreachable!(),
            Condition::RemoveCapability(place) => {
                place_capabilities.remove(place.into());
            }
            Condition::Unalloc(local) => {
                self[local] = CapabilityLocal::Unallocated;
            }
            Condition::AllocateOrDeallocate(local) => {
                self[local] = CapabilityLocal::Allocated(CapabilityProjections::new(local));
                place_capabilities.insert(local.into(), CapabilityKind::Write);
            }
            Condition::Capability(place, cap) => {
                place_capabilities.insert(place.into(), cap);
            }
        }
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    // TODO: Check that this is correct w.r.t capabilities
    pub(crate) fn place_to_collapse_to(
        &self,
        to: Place<'tcx>,
        _for_cap: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Place<'tcx> {
        for place in to.iter_places(repacker).into_iter().rev() {
            if self.contains_expansion_to(place, repacker) {
                return place;
            }
        }
        to.local.into()
    }

    #[tracing::instrument(skip(self, repacker))]
    fn repack(
        &mut self,
        to: Place<'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        for_cap: CapabilityKind,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let nearest_owned_place = to.nearest_owned_place(repacker);
        let collapse_to = self.place_to_collapse_to(nearest_owned_place, for_cap, repacker);
        tracing::debug!("Collapse to: {collapse_to:?} for {to:?}");
        let mut result = self.collapse(collapse_to, place_capabilities, repacker)?;
        tracing::debug!("Post collapse result: {result:?}");
        tracing::debug!("Post collapse self: {self:?}");
        let prefix = place_capabilities.get_longest_prefix(nearest_owned_place);
        if prefix != nearest_owned_place
            && !self.contains_expansion_to(nearest_owned_place, repacker)
        {
            result.extend(self.expand(
                prefix,
                CorrectedPlace::new(nearest_owned_place, repacker),
                for_cap,
                place_capabilities,
                repacker,
            )?);
        }
        if to != nearest_owned_place {
            match nearest_owned_place.ref_mutability(repacker) {
                Some(Mutability::Mut) => {
                    place_capabilities.remove(nearest_owned_place.into());
                }
                Some(Mutability::Not) => {
                    place_capabilities.insert(nearest_owned_place.into(), CapabilityKind::Read);
                }
                None => unreachable!(),
            }
        } else {
            let current_capability = match place_capabilities.get(to.into()) {
                Some(cap) => cap,
                None => {
                    // The loan for this place has just expired.
                    // TODO: Make interaction between borrow and owned PCG more robust.
                    place_capabilities.insert(to.into(), for_cap);
                    return Ok(result);
                    // let err_msg =
                    //     format!("Place {} has no capability", to.to_short_string(repacker));
                    // tracing::error!("{err_msg}");
                    // panic!("{err_msg}");
                }
            };
            if current_capability == CapabilityKind::Exclusive && for_cap == CapabilityKind::Write {
                result.push(RepackOp::Weaken(to, current_capability, for_cap));
                place_capabilities.insert(to.into(), for_cap);
            }
        }
        tracing::debug!("Result: {result:?}");
        tracing::debug!("Self: {self:?}");
        Ok(result)
    }
}
