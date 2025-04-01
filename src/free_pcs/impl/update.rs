// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    borrow_pcg::state::BorrowsState,
    combined_pcs::PcgError,
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections, RepackOp},
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
    pub(crate) fn get_capability(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        if let CapabilityLocal::Allocated(capability_projections) = &self[place.local] {
            capability_projections.get_capability(place)
        } else {
            None
        }
    }
    pub(crate) fn set_capability_if_allocated(
        &mut self,
        place: Place<'tcx>,
        cap: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        if let CapabilityLocal::Allocated(capability_projections) = &mut self[place.local] {
            capability_projections.set_capability(place, cap, repacker);
        }
    }

    #[tracing::instrument(skip(self, cond, repacker, borrows))]
    pub(crate) fn requires(
        &mut self,
        cond: Condition<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        borrows: &BorrowsState<'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        match cond {
            Condition::RemoveCapability(place) => {
                let cp = self[place.local].get_allocated_mut();
                cp.remove_capability(place);
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
                        *cap = CapabilityLocal::Allocated(CapabilityProjections::new_uninit(local));
                        Ok(vec![])
                    }
                    CapabilityLocal::Allocated(_) => self.requires(
                        Condition::Capability(local.into(), CapabilityKind::Write),
                        repacker,
                        borrows,
                    ),
                }
            }
            Condition::Capability(place, cap) => {
                let nearest_owned_place = place.nearest_owned_place(repacker);
                let cp = self[nearest_owned_place.local].get_allocated_mut();
                tracing::debug!("Repack to {nearest_owned_place:?} for {place:?} in {cp:?}");
                let result = cp.repack(place, repacker, cap)?;
                if nearest_owned_place != place {
                    match nearest_owned_place.ref_mutability(repacker) {
                        Some(Mutability::Mut) => {
                            cp.remove_capability(nearest_owned_place);
                        }
                        Some(Mutability::Not) => {
                            cp.set_capability(nearest_owned_place, CapabilityKind::Read, repacker);
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
                    self.check_pre_satisfied(pre, repacker);
                }
                Ok(vec![])
            }
        }
    }

    fn check_pre_satisfied(&self, pre: Condition<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) {
        match pre {
            Condition::RemoveCapability(_place) => {}
            Condition::Unalloc(local) => {
                assert!(
                    self[local].is_unallocated(),
                    "local: {local:?}, fpcs: {self:?}\n"
                );
            }
            Condition::AllocateOrDeallocate(_local) => {
                // TODO: This assertion fails for proc_macro2 crate, determine why
                // assert_eq!(
                //     self[local].get_allocated()[&local.into()],
                //     CapabilityKind::Write,
                //     "local: {local:?}, body: {:?}\n",
                //     repacker.body().source.def_id()
                // );
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
                    self.check_pre_satisfied(pre, repacker);
                }
            }
        }
    }
    pub(crate) fn ensures(&mut self, t: Triple<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) {
        self.check_pre_satisfied(t.pre(), repacker);
        let Some(post) = t.post() else {
            return;
        };
        match post {
            Condition::Return => unreachable!(),
            Condition::RemoveCapability(place) => {
                let cp = self[place.local].get_allocated_mut();
                cp.remove_capability(place);
            }
            Condition::Unalloc(local) => {
                self[local] = CapabilityLocal::Unallocated;
            }
            Condition::AllocateOrDeallocate(local) => {
                self[local] = CapabilityLocal::Allocated(CapabilityProjections::new_uninit(local));
            }
            Condition::Capability(place, cap) => {
                if place.is_owned(repacker) {
                    self[place.local]
                        .get_allocated_mut()
                        .set_capability(place, cap, repacker);
                }
            }
        }
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    fn get_longest_prefix(&self, to: Place<'tcx>) -> Place<'tcx> {
        self.place_capabilities()
            .iter()
            .flat_map(|(p, _)| p.try_into())
            .filter(|p: &Place| p.is_prefix(to))
            .max_by_key(|p| p.projection.len())
            .unwrap_or(self.get_local().into())
    }

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
        repacker: PlaceRepacker<'_, 'tcx>,
        for_cap: CapabilityKind,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let nearest_owned_place = to.nearest_owned_place(repacker);
        let collapse_to = self.place_to_collapse_to(nearest_owned_place, for_cap, repacker);
        tracing::debug!("Collapse to: {collapse_to:?} for {to:?}");
        let mut result = self.collapse(collapse_to, repacker)?;
        tracing::debug!("Post collapse result: {result:?}");
        tracing::debug!("Post collapse self: {self:?}");
        let prefix = self.get_longest_prefix(nearest_owned_place);
        if prefix != nearest_owned_place
            && !self.contains_expansion_to(nearest_owned_place, repacker)
        {
            result.extend(self.expand(
                prefix,
                CorrectedPlace::new(nearest_owned_place, repacker),
                for_cap,
                repacker,
            )?);
        }
        if to != nearest_owned_place {
            match nearest_owned_place.ref_mutability(repacker) {
                Some(Mutability::Mut) => {
                    self.remove_capability(nearest_owned_place);
                }
                Some(Mutability::Not) => {
                    self.set_capability(nearest_owned_place, CapabilityKind::Read, repacker);
                }
                None => unreachable!(),
            }
        } else {
            let current_capability = match self.get_capability(to) {
                Some(cap) => cap,
                None => {
                    // The loan for this place has just expired.
                    // TODO: Make interaction between borrow and owned PCG more robust.
                    self.set_capability(to, for_cap, repacker);
                    return Ok(result);
                    // let err_msg =
                    //     format!("Place {} has no capability", to.to_short_string(repacker));
                    // tracing::error!("{err_msg}");
                    // panic!("{err_msg}");
                }
            };
            if current_capability == CapabilityKind::Exclusive && for_cap == CapabilityKind::Write {
                result.push(RepackOp::Weaken(to, current_capability, for_cap));
                self.set_capability(to, for_cap, repacker);
            }
        }
        tracing::debug!("Result: {result:?}");
        tracing::debug!("Self: {self:?}");
        Ok(result)
    }
}
