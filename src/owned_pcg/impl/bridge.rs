// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    error::PcgError,
    owned_pcg::{LocalExpansions, OwnedPcg, OwnedPcgLocal, RepackOp},
    pcg::{CapabilityKind, place_capabilities::PlaceCapabilitiesInterface},
    utils::HasCompilerCtxt,
};

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn bridge<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &self,
        other: &Self,
        place_capabilities: &(impl PlaceCapabilitiesInterface<'tcx> + Clone),
        ctxt: Ctxt,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError>
    where
        'tcx: 'a,
    {
        if self.len() != other.len() {
            return Err(PcgError::internal(format!(
                "Capability summaries have different lengths: {} (previous) != {} (next)",
                self.len(),
                other.len()
            )));
        }
        let mut repacks = Vec::new();
        for (l, from) in self.iter_enumerated() {
            let local_repacks = from.bridge(&other[l], place_capabilities, ctxt)?;
            repacks.extend(local_repacks);
        }
        Ok(repacks)
    }
}

impl<'tcx> OwnedPcgLocal<'tcx> {
    pub(crate) fn bridge<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &self,
        other: &Self,
        place_capabilities: &(impl PlaceCapabilitiesInterface<'tcx> + Clone),
        ctxt: Ctxt,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError>
    where
        'tcx: 'a,
    {
        let mut place_capabilities = place_capabilities.clone();
        match (self, other) {
            (OwnedPcgLocal::Unallocated, OwnedPcgLocal::Unallocated) => Ok(Vec::new()),
            (OwnedPcgLocal::Allocated(from_places), OwnedPcgLocal::Allocated(to_places)) => {
                from_places.bridge(to_places, &place_capabilities, ctxt)
            }
            (OwnedPcgLocal::Allocated(cps), OwnedPcgLocal::Unallocated) => {
                let mut cps = cps.clone();
                let local = cps.get_local();
                let mut repacks = Vec::new();
                for (place, k) in place_capabilities.owned_capabilities(local, ctxt) {
                    if k.expect_concrete() > CapabilityKind::Write {
                        repacks.push(RepackOp::Weaken(
                            place,
                            k.expect_concrete(),
                            CapabilityKind::Write,
                        ));
                        *k = CapabilityKind::Write.into();
                    }
                }
                if cps.contains_expansion_from(local.into()) {
                    let packs = cps
                        .collapse(local.into(), None, &mut place_capabilities, ctxt)
                        .unwrap();
                    repacks.extend(packs);
                };
                repacks.push(RepackOp::StorageDead(local));
                Ok(repacks)
            }
            (OwnedPcgLocal::Unallocated, OwnedPcgLocal::Allocated(cps)) => {
                // A bit of an unusual case, should happen only when we
                // "allocated" a local to allow it to immediately be
                // StorageDead-ed. In this case we should ignore the SD.
                // assert_eq!(cps[&cps.get_local().into()], CapabilityKind::Write);
                Ok(vec![RepackOp::IgnoreStorageDead(cps.get_local())])
            }
        }
    }
}

impl<'tcx> LocalExpansions<'tcx> {
    pub(crate) fn bridge<Ctxt, C>(
        &self,
        _other: &Self,
        _self_place_capabilities: &impl PlaceCapabilitiesInterface<'tcx, C>,
        _ctxt: Ctxt,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        Ok(Vec::new())
    }
}
