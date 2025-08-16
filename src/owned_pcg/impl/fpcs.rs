// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    pcg::{
        CapabilityKind,
        ctxt::AnalysisCtxt,
        place_capabilities::{
            PlaceCapabilities, PlaceCapabilitiesInterface, SymbolicPlaceCapabilities,
        },
    },
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::mir::{self, Local, RETURN_PLACE},
    },
    utils::{HasCompilerCtxt, Place, data_structures::HashSet},
};
use derive_more::{Deref, DerefMut};

use crate::{owned_pcg::OwnedPcgLocal, utils::CompilerCtxt};

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The expansions of all locals.
pub struct OwnedPcg<'tcx>(IndexVec<Local, OwnedPcgLocal<'tcx>>);

impl Debug for OwnedPcg<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let v: Vec<_> = self.0.iter().filter(|c| !c.is_unallocated()).collect();
        v.fmt(f)
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn start_block<'a>(
        capabilities: &mut SymbolicPlaceCapabilities<'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Self {
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
        OwnedPcg(capability_summary)
    }
}

impl<'tcx> OwnedPcg<'tcx> {
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

    pub(crate) fn leaf_places<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
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
