// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    combined_pcs::PCGError,
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections, RepackOp},
    pcg_validity_assert,
    rustc_interface::middle::mir::{Local, RETURN_PLACE},
    utils::{corrected::CorrectedPlace, LocalMutationIsAllowed, Place, PlaceRepacker},
};

use super::{
    triple::{Condition, Triple},
    CapabilitySummary, RelatedSet,
};

impl<'tcx> CapabilitySummary<'tcx> {
    pub(crate) fn set_capability(&mut self, place: Place<'tcx>, cap: CapabilityKind) {
        self[place.local]
            .get_allocated_mut()
            .set_capability(place, cap)
    }

    pub(crate) fn requires(
        &mut self,
        cond: Condition<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PCGError> {
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
                    ),
                }
            }
            Condition::Capability(place, cap) => {
                let cp = self[place.local].get_allocated_mut();
                let result = cp.repack(place, repacker, cap)?;
                cp.set_capability(place, cap);
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
                        assert!(!place.projects_shared_ref(repacker));
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
                self[place.local]
                    .get_allocated_mut()
                    .set_capability(place, cap);
            }
        }
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    fn get_longest_prefix(&self, to: Place<'tcx>) -> Place<'tcx> {
        self.place_capabilities()
            .iter()
            .filter(|(p, _)| p.is_prefix(to))
            .max_by_key(|(p, _)| p.projection.len())
            .map(|(p, _)| *p)
            .unwrap_or(self.get_local().into())
    }

    pub(crate) fn place_to_collapse_to(
        &self,
        to: Place<'tcx>,
        for_cap: CapabilityKind,
    ) -> Place<'tcx> {
        let related = self.find_all_related(to);
        related.place_to_collapse_to(to, for_cap)
    }

    pub(crate) fn find_all_related(&self, to: Place<'tcx>) -> RelatedSet<'tcx> {
        RelatedSet::new(
            self.place_capabilities()
                .iter()
                .filter(|(p, _)| (*p).partial_cmp(&to).is_some())
                .map(|(p, c)| (*p, *c))
                .collect(),
        )
    }

    #[tracing::instrument(skip(self, repacker))]
    pub(super) fn repack(
        &mut self,
        to: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        for_cap: CapabilityKind,
    ) -> Result<Vec<RepackOp<'tcx>>, PCGError> {
        // TODO
        // if !to.is_owned(repacker) {
        // panic!("Cannot repack to borrowed place {:?}", to);
        // }
        let collapse_to = self.place_to_collapse_to(to, for_cap);
        // eprintln!("Collapse to {collapse_to:?} for repack to {to:?} in {self:?}");
        let mut result = self.collapse(collapse_to, repacker)?;
        tracing::debug!("Post collapse result: {result:?}");
        tracing::debug!("Post collapse self: {self:?}");
        let prefix = self.get_longest_prefix(to);
        if prefix != to && self.get_capability(to).is_none() {
            result.extend(self.expand(
                prefix,
                CorrectedPlace::new(to, repacker),
                for_cap,
                repacker,
            )?);
        }
        tracing::debug!("Result: {result:?}");
        tracing::debug!("Self: {self:?}");
        Ok(result)
    }
}
