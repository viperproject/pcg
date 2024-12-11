// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections},
    rustc_interface::middle::mir::{Local, RETURN_PLACE, START_BLOCK},
    utils::{LocalMutationIsAllowed, Place, PlaceOrdering, PlaceRepacker},
};

use super::{
    triple::{Condition, Triple},
    CapabilitySummary,
};

impl<'tcx> CapabilitySummary<'tcx> {
    pub(crate) fn requires(&mut self, cond: Condition<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) {
        match cond {
            Condition::Unalloc(_) => {}
            Condition::AllocateOrDeallocate(local) => {
                match &mut self[local] {
                    cap @ CapabilityLocal::Unallocated => {
                        // A bit of an unusual case: we're at a StorageDead but
                        // already deallocated. Allocate now so that the
                        // precondition of SD can be met, but we'll catch this in
                        // `bridge` and emit a IgnoreSD op.
                        *cap = CapabilityLocal::Allocated(CapabilityProjections::new_uninit(local));
                    }
                    CapabilityLocal::Allocated(_) => self.requires(
                        Condition::Capability(local.into(), CapabilityKind::Write),
                        repacker,
                    ),
                }
            }
            Condition::Capability(place, cap) => {
                let cp = self[place.local].get_allocated_mut();
                cp.repack(place, repacker);
                if cp[&place].is_exclusive() && cap.is_write() {
                    // Requires write should deinit an exclusive
                    cp.insert(place, cap);
                } else if cp[&place].is_lent_exclusive()
                    && (cap.is_read() || cap.is_exclusive())
                {
                    // This read will expire the loan, so we regain exclusive access
                    // TODO: If we expire borrows eagerly, perhaps we don't need this logic
                    cp.insert(place, CapabilityKind::Exclusive);
                } else {
                    // TODO
                }
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
                    self.requires(pre, repacker);
                }
            }
        }
    }

    fn check_pre_satisfied(&self, pre: Condition<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) {
        match pre {
            Condition::Unalloc(local) => {
                assert!(
                    self[local].is_unallocated(),
                    "local: {local:?}, fpcs: {self:?}\n"
                );
            }
            Condition::AllocateOrDeallocate(local) => {
                assert_eq!(
                    self[local].get_allocated()[&local.into()],
                    CapabilityKind::Write,
                    "local: {local:?}, body: {:?}\n",
                    repacker.body().source.def_id()
                );
            }
            Condition::Capability(place, cap) => {
                match cap {
                    CapabilityKind::Read | CapabilityKind::Lent => {
                        // TODO
                    }
                    CapabilityKind::Write => {
                        // Cannot get write on a shared ref
                        debug_assert!(place
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
            Condition::Unalloc(local) => {
                self[local] = CapabilityLocal::Unallocated;
            }
            Condition::AllocateOrDeallocate(local) => {
                self[local] = CapabilityLocal::Allocated(CapabilityProjections::new_uninit(local));
            }
            Condition::Capability(place, cap) => {
                self[place.local].get_allocated_mut().update_cap(place, cap);
            }
        }
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    pub(super) fn repack(&mut self, to: Place<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) {
        let related = self.find_all_related(to, None);
        for (from_place, _) in (*related).iter().copied() {
            match from_place.partial_cmp(to).unwrap() {
                PlaceOrdering::Prefix => {
                    self.expand(related.get_only_place(), to, repacker);
                }
                PlaceOrdering::Equal => (),
                PlaceOrdering::Suffix => {
                    eprintln!("Places: {:?}", related.get_places());
                    self.collapse(related.get_places(), to, repacker);
                    return;
                }
                PlaceOrdering::Both => {
                    let cp = related.common_prefix(to);
                    // Collapse
                    self.collapse(related.get_places(), cp, repacker);
                    // Expand
                    self.expand(cp, to, repacker);
                }
            }
        }
    }
}
