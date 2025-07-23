// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    free_pcs::RepackOp,
    pcg::{
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
        PcgError,
    },
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::mir::{self, Local, RETURN_PLACE},
    },
    utils::{data_structures::HashSet, Place},
};
use derive_more::{Deref, DerefMut};

use super::CapabilityKind;
use crate::{
    free_pcs::{OwnedPcgRoot, PlaceExpansions},
    utils::CompilerCtxt,
};

#[deprecated(note = "Use `OwnedPcg` instead")]
pub type FreePlaceCapabilitySummary<'tcx> = OwnedPcg<'tcx>;

/// The state of the Owned PCG.
#[derive(Clone, Default)]
pub struct OwnedPcg<'tcx> {
    pub(crate) data: Option<LocalExpansions<'tcx>>,
}

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn contains_expansion_from(&self, place: Place<'tcx>) -> bool {
        self.locals()[place.local]
            .get_allocated()
            .expansions()
            .iter()
            .any(|pe| pe.base_place() == place)
    }

    pub(crate) fn leaf_places(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> HashSet<Place<'tcx>> {
        self.data.as_ref().unwrap().leaf_places(ctxt)
    }

    pub fn locals(&self) -> &LocalExpansions<'tcx> {
        self.data.as_ref().unwrap()
    }

    pub(crate) fn locals_mut(&mut self) -> &mut LocalExpansions<'tcx> {
        self.data.as_mut().unwrap()
    }

    pub(crate) fn bridge(
        &self,
        other: &Self,
        place_capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        self.data.as_ref().unwrap().bridge(
            other.data.as_ref().unwrap(),
            place_capabilities,
            repacker,
        )
    }

    pub(crate) fn initialize_as_start_block(
        &mut self,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        let always_live = repacker.always_live_locals();
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(repacker.body().arg_count);
        let capability_summary = IndexVec::from_fn_n(
            |local: mir::Local| {
                if local == return_local {
                    capabilities.insert(local.into(), CapabilityKind::Write, repacker);
                    OwnedPcgRoot::new(local)
                } else if local <= last_arg {
                    capabilities.insert(local.into(), CapabilityKind::Exclusive, repacker);
                    OwnedPcgRoot::new(local)
                } else if always_live.contains(local) {
                    capabilities.insert(local.into(), CapabilityKind::Write, repacker);
                    OwnedPcgRoot::new(local)
                } else {
                    // Other locals are unallocated
                    OwnedPcgRoot::Unallocated
                }
            },
            repacker.local_count(),
        );
        self.data = Some(LocalExpansions(capability_summary));
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

#[deprecated(note = "Use `LocalExpansions` instead")]
pub type CapabilityLocals<'tcx> = LocalExpansions<'tcx>;

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The expansions of all locals.
pub struct LocalExpansions<'tcx>(IndexVec<Local, OwnedPcgRoot<'tcx>>);

impl Debug for LocalExpansions<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let v: Vec<_> = self.0.iter().filter(|c| !c.is_unallocated()).collect();
        v.fmt(f)
    }
}

impl<'tcx> LocalExpansions<'tcx> {
    pub(crate) fn leaf_places(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> HashSet<Place<'tcx>> {
        self.0
            .iter()
            .filter(|c| !c.is_unallocated())
            .flat_map(|c| c.get_allocated().leaves(ctxt))
            .collect()
    }
    pub(crate) fn expansions(&self) -> Vec<&PlaceExpansions<'tcx>> {
        self.0
            .iter()
            .filter(|c| !c.is_unallocated())
            .map(|c| c.get_allocated())
            .collect()
    }
}
