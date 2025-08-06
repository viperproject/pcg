// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    free_pcs::{CapabilityKind, OwnedPcgLocal, OwnedPcgData, LocalExpansions, RepackOp},
    pcg::{
        PcgError,
        place_capabilities::PlaceCapabilities,
    },
    utils::CompilerCtxt,
};

impl<'tcx> OwnedPcgData<'tcx> {
    pub(crate) fn bridge(
        &self,
        other: &Self,
        place_capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        if self.len() != other.len() {
            return Err(PcgError::internal(format!(
                "Capability summaries have different lengths: {} (previous) != {} (next)",
                self.len(),
                other.len()
            )));
        }
        let mut repacks = Vec::new();
        for (l, from) in self.iter_enumerated() {
            let local_repacks = from.bridge(&other[l], place_capabilities, repacker)?;
            repacks.extend(local_repacks);
        }
        Ok(repacks)
    }
}

impl<'tcx> OwnedPcgLocal<'tcx> {
    pub(crate) fn bridge(
        &self,
        other: &Self,
        place_capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut place_capabilities = place_capabilities.clone();
        match (self, other) {
            (OwnedPcgLocal::Unallocated, OwnedPcgLocal::Unallocated) => Ok(Vec::new()),
            (OwnedPcgLocal::Allocated(from_places), OwnedPcgLocal::Allocated(to_places)) => {
                from_places.bridge(to_places, &place_capabilities, repacker)
            }
            (OwnedPcgLocal::Allocated(cps), OwnedPcgLocal::Unallocated) => {
                let mut cps = cps.clone();
                let local = cps.get_local();
                let mut repacks = Vec::new();
                for (place, k) in place_capabilities.owned_capabilities(local, repacker) {
                    if *k > CapabilityKind::Write {
                        repacks.push(RepackOp::Weaken(place, *k, CapabilityKind::Write));
                        *k = CapabilityKind::Write;
                    }
                }
                if cps.contains_expansion_from(local.into()) {
                    let packs = cps
                        .collapse(local.into(), None, &mut place_capabilities, repacker)
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
    pub(crate) fn bridge(
        &self,
        other: &Self,
        self_place_capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        Ok(Vec::new())
    }
}
