// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cmp::Ordering;

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections},
    pcg::{
        place_capabilities::PlaceCapabilities,
        triple::{PlaceCondition, Triple},
    },
    pcg_validity_assert,
    utils::{
        CompilerCtxt,
        LocalMutationIsAllowed,
    },
};

use super::CapabilityLocals;

impl<'tcx> CapabilityLocals<'tcx> {

    #[tracing::instrument(skip(self, capabilities, repacker))]
    fn check_pre_satisfied(
        &self,
        pre: PlaceCondition<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        match pre {
            PlaceCondition::ExpandTwoPhase(_place) => {}
            PlaceCondition::RemoveCapability(_place) => {}
            PlaceCondition::Unalloc(local) => {
                assert!(
                    self[local].is_unallocated(),
                    "local: {local:?}, fpcs: {self:?}\n"
                );
            }
            PlaceCondition::AllocateOrDeallocate(_local) => {}
            PlaceCondition::Capability(place, required_cap) => {
                match required_cap {
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
                        // TODO
                        // assert!(
                        //     !place.projects_shared_ref(repacker),
                        //     "Cannot get exclusive on projection of shared ref {}",
                        //     place.to_short_string(repacker)
                        // );
                    }
                    CapabilityKind::ShallowExclusive => unreachable!(),
                }
                if place.is_owned(repacker) {
                    if let Some(current_cap) = capabilities.get(place.into()) {
                        pcg_validity_assert!(
                            matches!(
                                current_cap.partial_cmp(&required_cap),
                                Some(Ordering::Equal) | Some(Ordering::Greater)
                            ),
                            "Capability {current_cap:?} is not >= {required_cap:?} for {place:?}"
                        )
                    } else {
                        pcg_validity_assert!(false, "No capability for {place:?}");
                    }
                }
            }
            PlaceCondition::Return => {
                // assert!(
                //     capabilities.get(RETURN_PLACE.into()).unwrap() == CapabilityKind::Exclusive,
                // );
            }
        }
    }
    #[tracing::instrument(skip(self, place_capabilities))]
    pub(crate) fn ensures(
        &mut self,
        t: Triple<'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
    ) {
        let Some(post) = t.post() else {
            return;
        };
        match post {
            PlaceCondition::Return => unreachable!(),
            PlaceCondition::RemoveCapability(place) => {
                place_capabilities.remove(place.into());
            }
            PlaceCondition::Unalloc(local) => {
                self[local] = CapabilityLocal::Unallocated;
            }
            PlaceCondition::AllocateOrDeallocate(local) => {
                self[local] = CapabilityLocal::Allocated(CapabilityProjections::new(local));
                place_capabilities.insert(local.into(), CapabilityKind::Write);
            }
            PlaceCondition::Capability(place, cap) => {
                place_capabilities.insert(place.into(), cap);
            }
            PlaceCondition::ExpandTwoPhase(place) => {
                place_capabilities.insert(place.into(), CapabilityKind::Read);
            }
        }
    }
}
