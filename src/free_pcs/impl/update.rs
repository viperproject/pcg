// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cmp::Ordering;

use crate::{
    action::PcgActions,
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections, RepackOp},
    pcg::{place_capabilities::PlaceCapabilities, PCGUnsupportedError, PcgError},
    pcg_validity_assert,
    rustc_interface::{ast::Mutability, middle::mir::RETURN_PLACE},
    utils::{
        corrected::CorrectedPlace, display::DisplayWithCompilerCtxt, CompilerCtxt,
        LocalMutationIsAllowed, Place,
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
        repacker: CompilerCtxt<'_, 'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        let ops = match cond {
            Condition::RemoveCapability(place) => {
                place_capabilities.remove(place.into());
                PcgActions::default()
            }
            Condition::Unalloc(_) => PcgActions::default(),
            Condition::AllocateOrDeallocate(local) => {
                self[local] = CapabilityLocal::Allocated(CapabilityProjections::new(local));
                place_capabilities.insert(local.into(), CapabilityKind::Write);
                PcgActions::default()
            }
            Condition::Capability(place, cap) => {
                if place.contains_unsafe_deref(repacker) {
                    return Err(PcgError::unsupported(PCGUnsupportedError::DerefUnsafePtr));
                }
                let nearest_owned_place = place.nearest_owned_place(repacker);
                let cp = self[nearest_owned_place.local].get_allocated_mut();
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
            Condition::Return => PcgActions::default(),
        };
        self.check_pre_satisfied(cond, place_capabilities, repacker);
        Ok(ops)
    }

    #[tracing::instrument(skip(self, capabilities, repacker))]
    fn check_pre_satisfied(
        &self,
        pre: Condition<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
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
            Condition::Return => {
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
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Place<'tcx> {
        for place in to.iter_places(repacker).into_iter().rev() {
            if self.contains_expansion_to(place, repacker) {
                return place;
            }
        }
        to.local.into()
    }

    fn get_longest_prefix(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> Place<'tcx> {
        let mut current = place;
        while !self.contains_expansion_to(current, ctxt) {
            current = current.parent_place().unwrap();
        }
        current
    }

    #[tracing::instrument(skip(self, ctxt))]
    fn repack(
        &mut self,
        to: Place<'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
        for_cap: CapabilityKind,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        let nearest_owned_place = to.nearest_owned_place(ctxt);
        let collapse_to = self.place_to_collapse_to(nearest_owned_place, for_cap, ctxt);
        tracing::debug!("Collapse to: {collapse_to:?} for {to:?}");
        let mut result = if for_cap != CapabilityKind::Read {
            self.collapse(collapse_to, place_capabilities, ctxt)?
        } else {
            vec![]
        };
        tracing::debug!("Post collapse result: {result:?}");
        tracing::debug!("Post collapse self: {self:?}");
        let prefix = self.get_longest_prefix(nearest_owned_place, ctxt);
        if prefix != nearest_owned_place && !self.contains_expansion_to(nearest_owned_place, ctxt) {
            result.extend(self.expand(
                prefix,
                CorrectedPlace::new(nearest_owned_place, ctxt),
                for_cap,
                place_capabilities,
                ctxt,
            )?);
        }
        // TODO: Handle upgrading to read properly by ensuring that the node is a leaf
        // and removing read perms from the parents
        if (for_cap == CapabilityKind::Exclusive || for_cap == CapabilityKind::Write)
            && place_capabilities.get(to.into()) == Some(CapabilityKind::Read)
        {
            place_capabilities.insert(to.into(), CapabilityKind::Exclusive);
        }
        if to != nearest_owned_place {
            match nearest_owned_place.ref_mutability(ctxt) {
                Some(Mutability::Mut) => {
                    place_capabilities.remove(nearest_owned_place.into());
                }
                Some(Mutability::Not) => {
                    place_capabilities.insert(nearest_owned_place.into(), CapabilityKind::Read);
                }
                None => panic!(
                    "Repack {}: No mutability for {}: {:?}",
                    to.to_short_string(ctxt),
                    nearest_owned_place.to_short_string(ctxt),
                    nearest_owned_place.ty(ctxt)
                ),
            }
        } else {
            let current_capability = match place_capabilities.get(to.into()) {
                Some(cap) => cap,
                None => {
                    // The loan for this place has just expired.
                    // TODO: Make interaction between borrow and owned PCG more robust.
                    place_capabilities.insert(to.into(), for_cap);
                    return Ok(result.into());
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
        Ok(result.into())
    }
}
