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
        display::DisplayWithCompilerCtxt, CompilerCtxt,
        LocalMutationIsAllowed,
    },
};

use super::CapabilityLocals;

impl<'tcx> CapabilityLocals<'tcx> {
    // #[tracing::instrument(skip(self, repacker, place_capabilities))]
    // pub(crate) fn requires(
    //     &mut self,
    //     cond: PlaceCondition<'tcx>,
    //     repacker: CompilerCtxt<'_, 'tcx>,
    //     place_capabilities: &mut PlaceCapabilities<'tcx>,
    // ) -> Result<PcgActions<'tcx>, PcgError> {
    //     let ops = match cond {
    //         PlaceCondition::RemoveCapability(place) => {
    //             place_capabilities.remove(place.into());
    //             PcgActions::default()
    //         }
    //         PlaceCondition::Unalloc(_) => PcgActions::default(),
    //         PlaceCondition::AllocateOrDeallocate(local) => {
    //             self[local] = CapabilityLocal::Allocated(CapabilityProjections::new(local));
    //             place_capabilities.insert(local.into(), CapabilityKind::Write);
    //             PcgActions::default()
    //         }
    //         PlaceCondition::Capability(place, cap) => {
    //             if place.contains_unsafe_deref(repacker) {
    //                 return Err(PcgError::unsupported(PCGUnsupportedError::DerefUnsafePtr));
    //             }
    //             let nearest_owned_place = place.nearest_owned_place(repacker);
    //             let cp = self[nearest_owned_place.local].get_allocated_mut();
    //             let result = cp.repack(place, place_capabilities, repacker, cap)?;
    //             if nearest_owned_place != place {
    //                 match nearest_owned_place.ref_mutability(repacker) {
    //                     Some(Mutability::Mut) => {
    //                         place_capabilities.remove(nearest_owned_place.into());
    //                     }
    //                     Some(Mutability::Not) => {
    //                         place_capabilities
    //                             .insert(nearest_owned_place.into(), CapabilityKind::Read);
    //                     }
    //                     None => unreachable!(),
    //                 }
    //             }
    //             result
    //         }
    //         PlaceCondition::Return => PcgActions::default(),
    //     };
    //     self.check_pre_satisfied(cond, place_capabilities, repacker);
    //     Ok(ops)
    // }

    #[tracing::instrument(skip(self, capabilities, repacker))]
    fn check_pre_satisfied(
        &self,
        pre: PlaceCondition<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        match pre {
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
                        assert!(
                            !place.projects_shared_ref(repacker),
                            "Cannot get exclusive on projection of shared ref {}",
                            place.to_short_string(repacker)
                        );
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
        }
    }
}
