// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, LocalExpansions},
    pcg::{
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
        triple::{PlaceCondition, Triple},
    },
    pcg_validity_assert,
    utils::{CompilerCtxt, LocalMutationIsAllowed, display::DisplayWithCompilerCtxt},
};

use crate::rustc_interface::middle::mir::RETURN_PLACE;

use super::CapabilityLocals;

impl<'tcx> CapabilityLocals<'tcx> {
    fn check_pre_satisfied(
        &self,
        pre: PlaceCondition<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        match pre {
            PlaceCondition::ExpandTwoPhase(_place) => {}
            PlaceCondition::Unalloc(local) => {
                pcg_validity_assert!(
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
                        pcg_validity_assert!(
                            place.is_mutable(LocalMutationIsAllowed::Yes, ctxt).is_ok()
                        );
                    }
                    CapabilityKind::Exclusive => {
                        // Cannot get exclusive on a shared ref
                        pcg_validity_assert!(
                            !place.projects_shared_ref(ctxt),
                            "Cannot get exclusive on projection of shared ref {}",
                            place.to_short_string(ctxt)
                        );
                    }
                    CapabilityKind::ShallowExclusive => unreachable!(),
                }
                if place.is_owned(ctxt) {
                    if capabilities.get(place).is_some() {
                        // pcg_validity_assert!(
                        //     matches!(
                        //         current_cap.partial_cmp(&required_cap),
                        //         Some(Ordering::Equal) | Some(Ordering::Greater)
                        //     ),
                        //     "Capability {current_cap:?} is not >= {required_cap:?} for {place:?}"
                        // )
                    } else {
                        pcg_validity_assert!(false, "No capability for {}", place.to_short_string(ctxt));
                    }
                }
            }
            PlaceCondition::Return => {
                pcg_validity_assert!(
                    capabilities.get(RETURN_PLACE.into()).unwrap() == CapabilityKind::Exclusive
                );
            }
            PlaceCondition::RemoveCapability(_) => unreachable!(),
        }
    }
    pub(crate) fn ensures(
        &mut self,
        t: Triple<'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        self.check_pre_satisfied(t.pre(), place_capabilities, ctxt);
        let Some(post) = t.post() else {
            return;
        };
        match post {
            PlaceCondition::Return => unreachable!(),
            PlaceCondition::Unalloc(local) => {
                self[local] = CapabilityLocal::Unallocated;
                place_capabilities.remove_all_for_local(local, ctxt);
            }
            PlaceCondition::AllocateOrDeallocate(local) => {
                self[local] = CapabilityLocal::Allocated(LocalExpansions::new(local));
                place_capabilities.insert(local.into(), CapabilityKind::Write, ctxt);
            }
            PlaceCondition::Capability(place, cap) => {
                place_capabilities.insert(place, cap, ctxt);
            }
            PlaceCondition::ExpandTwoPhase(place) => {
                place_capabilities.insert(place, CapabilityKind::Read, ctxt);
            }
            PlaceCondition::RemoveCapability(place) => {
                place_capabilities.remove(place, ctxt);
            }
        }
    }
}
