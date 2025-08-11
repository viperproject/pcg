// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    free_pcs::RepackOp,
    pcg::{
        PcgError,
        ctxt::AnalysisCtxt,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::mir::{self, Local, RETURN_PLACE},
    },
    utils::{Place, data_structures::HashSet},
};
use derive_more::{Deref, DerefMut};

use super::CapabilityKind;
use crate::{free_pcs::OwnedPcgLocal, utils::CompilerCtxt};

/// The state of the Owned PCG.
#[derive(Clone, Default)]
pub struct OwnedPcg<'tcx> {
    pub(crate) data: Option<OwnedPcgData<'tcx>>,
}

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn check_validity(
        &self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), String> {
        self.data
            .as_ref()
            .unwrap()
            .check_validity(capabilities, ctxt)
    }

    pub(crate) fn is_allocated(&self, local: Local) -> bool {
        self.data.as_ref().unwrap().is_allocated(local)
    }

    pub(crate) fn contains_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.data.as_ref().unwrap().contains_place(place, ctxt)
    }

    pub(crate) fn leaf_places(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> HashSet<Place<'tcx>> {
        self.data.as_ref().unwrap().leaf_places(ctxt)
    }

    pub fn locals(&self) -> &OwnedPcgData<'tcx> {
        self.data.as_ref().unwrap()
    }

    pub(crate) fn locals_mut(&mut self) -> &mut OwnedPcgData<'tcx> {
        self.data.as_mut().unwrap()
    }

    pub(crate) fn bridge(
        &self,
        other: &Self,
        place_capabilities: &PlaceCapabilities<'tcx>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        self.data
            .as_ref()
            .unwrap()
            .bridge(other.data.as_ref().unwrap(), place_capabilities, ctxt)
    }

    pub(crate) fn initialize_as_start_block(
        &mut self,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) {
        let always_live = ctxt.ctxt.always_live_locals();
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(ctxt.body().arg_count);
        let capability_summary = IndexVec::from_fn_n(
            |local: mir::Local| {
                if local == return_local {
                    capabilities.insert(local.into(), CapabilityKind::Write, ctxt);
                    OwnedPcgLocal::new(local)
                } else if local <= last_arg {
                    capabilities.insert(local.into(), CapabilityKind::Exclusive, ctxt);
                    OwnedPcgLocal::new(local)
                } else if always_live.contains(local) {
                    capabilities.insert(local.into(), CapabilityKind::Write, ctxt);
                    OwnedPcgLocal::new(local)
                } else {
                    // Other locals are unallocated
                    OwnedPcgLocal::Unallocated
                }
            },
            ctxt.ctxt.local_count(),
        );
        self.data = Some(OwnedPcgData(capability_summary));
    }
}

impl PartialEq for OwnedPcg<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}
impl Eq for OwnedPcg<'_> {}

impl Debug for OwnedPcg<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.data.fmt(f)
    }
}
#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The expansions of all locals.
pub struct OwnedPcgData<'tcx>(IndexVec<Local, OwnedPcgLocal<'tcx>>);

impl Debug for OwnedPcgData<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let v: Vec<_> = self.0.iter().filter(|c| !c.is_unallocated()).collect();
        v.fmt(f)
    }
}

impl<'tcx> OwnedPcgData<'tcx> {
    pub(crate) fn check_validity(
        &self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), String> {
        self.0
            .iter()
            .try_for_each(|c| c.check_validity(capabilities, ctxt))
    }

    pub(crate) fn num_locals(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn leaf_places(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> HashSet<Place<'tcx>> {
        self.0
            .iter()
            .filter(|c| !c.is_unallocated())
            .flat_map(|c| c.get_allocated().leaf_places(ctxt))
            .collect()
    }

    pub(crate) fn contains_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        let expansion = &self.0[place.local];
        if expansion.is_unallocated() {
            return false;
        }
        expansion.get_allocated().contains_place(place, ctxt)
    }

    pub(crate) fn is_allocated(&self, local: Local) -> bool {
        !self.0[local].is_unallocated()
    }

    pub(crate) fn allocated_locals(&self) -> Vec<mir::Local> {
        self.0
            .iter_enumerated()
            .filter_map(|(i, c)| if !c.is_unallocated() { Some(i) } else { None })
            .collect()
    }
}
