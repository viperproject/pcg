// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cmp::Ordering;

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections, RepackOp},
    pcg::{place_capabilities::PlaceCapabilities, PcgError},
    pcg_validity_assert,
    rustc_interface::{
        ast::Mutability,
        middle::mir::RETURN_PLACE,
    },
    utils::{
        corrected::CorrectedPlace, display::DisplayWithCompilerCtxt, LocalMutationIsAllowed, Place,
        CompilerCtxt,
    },
};

use super::{
    triple::{Condition, Triple},
    CapabilityLocals,
};

impl<'tcx> CapabilityLocals<'tcx> {
    #[tracing::instrument(skip(self, repacker, place_capabilities))]
    pub(crate) fn requires(
        &mut self,
        cond: Condition<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx,'_>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let ops = match cond {
            Condition::RemoveCapability(place) => {
                place_capabilities.remove(place.into());
                vec![]
            }
            Condition::Unalloc(_) => vec![],
            Condition::AllocateOrDeallocate(local) => {
                self[local] = CapabilityLocal::Allocated(CapabilityProjections::new(local));
                place_capabilities.insert(local.into(), CapabilityKind::Write);
                vec![]
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
                result
            }
            Condition::Return => vec![],
        };
        self.check_pre_satisfied(cond, place_capabilities, repacker);
        Ok(ops)
    }

    #[tracing::instrument(skip(self, capabilities, repacker))]
    fn check_pre_satisfied(
        &self,
        pre: Condition<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx,'_>,
    ) {
        match pre {
            Condition::RemoveCapability(_place) => {}
            Condition::Unalloc(local) => {
                assert!(
                    self[local].is_unallocated(),
                    "local: {local:?}, fpcs: {self:?}\n"
                );
            }
            Condition::AllocateOrDeallocate(_local) => {}
            Condition::Capability(place, required_cap) => {
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
                        if matches!(
                            current_cap.partial_cmp(&required_cap),
                            Some(Ordering::Less) | None
                        ) {
                            tracing::error!(
                            "Capability {current_cap:?} is not >= {required_cap:?} for {place:?}"
                        );
                        }
                    } else {
                        tracing::error!("No capability for {place:?}");
                    }
                }
            }
            Condition::Return => {
                assert!(
                    capabilities.get(RETURN_PLACE.into()).unwrap() == CapabilityKind::Exclusive,
                );
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
        repacker: CompilerCtxt<'_, 'tcx,'_>,
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
        repacker: CompilerCtxt<'_, 'tcx,'_>,
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
