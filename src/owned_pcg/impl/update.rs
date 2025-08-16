// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    owned_pcg::{LocalExpansions, OwnedPcgLocal},
    pcg::{
        CapabilityKind,
        place_capabilities::{
            PlaceCapabilitiesInterface, PlaceCapabilitiesReader, SymbolicPlaceCapabilities,
        },
        triple::{PlaceCondition, Triple},
    },
    pcg_validity_assert,
    utils::{HasBorrowCheckerCtxt, LocalMutationIsAllowed, display::DisplayWithCompilerCtxt},
};

use crate::rustc_interface::middle::mir::RETURN_PLACE;

use super::OwnedPcg;

impl<'tcx> OwnedPcg<'tcx> {
    fn check_pre_satisfied<'a>(
        &self,
        pre: PlaceCondition<'tcx>,
        capabilities: &SymbolicPlaceCapabilities<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
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
                            place.to_short_string(ctxt.bc_ctxt())
                        );
                    }
                    CapabilityKind::ShallowExclusive => unreachable!(),
                }
                if place.is_owned(ctxt) {
                    if capabilities.get(place, ctxt).is_some() {
                        // pcg_validity_assert!(
                        //     matches!(
                        //         current_cap.partial_cmp(&required_cap),
                        //         Some(Ordering::Equal) | Some(Ordering::Greater)
                        //     ),
                        //     "Capability {current_cap:?} is not >= {required_cap:?} for {place:?}"
                        // )
                    } else {
                        pcg_validity_assert!(
                            false,
                            [ctxt],
                            "No capability for {}",
                            place.to_short_string(ctxt.bc_ctxt())
                        );
                    }
                }
            }
            PlaceCondition::Return => {
                pcg_validity_assert!(
                    capabilities.get(RETURN_PLACE.into(), ctxt).unwrap()
                        == CapabilityKind::Exclusive.into(),
                    [ctxt]
                );
            }
            PlaceCondition::RemoveCapability(_) => unreachable!(),
        }
    }
    pub(crate) fn ensures<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        t: Triple<'tcx>,
        place_capabilities: &mut SymbolicPlaceCapabilities<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        self.check_pre_satisfied(t.pre(), place_capabilities, ctxt);
        let Some(post) = t.post() else {
            return;
        };
        match post {
            PlaceCondition::Return => unreachable!(),
            PlaceCondition::Unalloc(local) => {
                self[local] = OwnedPcgLocal::Unallocated;
                place_capabilities.remove_all_for_local(local, ctxt);
            }
            PlaceCondition::AllocateOrDeallocate(local) => {
                self[local] = OwnedPcgLocal::Allocated(LocalExpansions::new(local));
                place_capabilities.insert(local.into(), CapabilityKind::Write, ctxt);
            }
            PlaceCondition::Capability(place, cap) => {
                place_capabilities.insert(place, cap, ctxt);
                // It's possible that the place could have been already expanded
                // exclusively (when it could have originally been expanded for
                // read), in which case we pretend we did the right thing all
                // along
                if cap == CapabilityKind::Read {
                    for (p, _) in place_capabilities
                        .capabilities_for_strict_postfixes_of(place)
                        .collect::<Vec<_>>()
                    {
                        place_capabilities.insert(p, CapabilityKind::Read, ctxt);
                    }
                }
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
