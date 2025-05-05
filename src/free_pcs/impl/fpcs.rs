// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    free_pcs::RepackOp,
    pcg::{place_capabilities::PlaceCapabilities, PcgError},
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::mir::{self, Local, RETURN_PLACE},
    },
};
use derive_more::{Deref, DerefMut};

use super::CapabilityKind;
use crate::{
    free_pcs::{CapabilityLocal, CapabilityProjections},
    utils::CompilerCtxt,
};

#[derive(Clone, Default)]
pub struct FreePlaceCapabilitySummary<'tcx> {
    pub(crate) data: Option<CapabilityLocals<'tcx>>,
}

impl<'tcx> FreePlaceCapabilitySummary<'tcx> {
    pub fn locals(&self) -> &CapabilityLocals<'tcx> {
        self.data.as_ref().unwrap()
    }

    pub(crate) fn locals_mut(&mut self) -> &mut CapabilityLocals<'tcx> {
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

    pub fn initialize_as_start_block(
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
                    capabilities.insert(local.into(), CapabilityKind::Write);
                    CapabilityLocal::new(local)
                } else if local <= last_arg {
                    capabilities.insert(local.into(), CapabilityKind::Exclusive);
                    CapabilityLocal::new(local)
                } else if always_live.contains(local) {
                    capabilities.insert(local.into(), CapabilityKind::Write);
                    CapabilityLocal::new(local)
                } else {
                    // Other locals are unallocated
                    CapabilityLocal::Unallocated
                }
            },
            repacker.local_count(),
        );
        self.data = Some(CapabilityLocals(capability_summary));
    }
}

impl PartialEq for FreePlaceCapabilitySummary<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}
impl Eq for FreePlaceCapabilitySummary<'_> {}

impl Debug for FreePlaceCapabilitySummary<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.data.fmt(f)
    }
}
#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The free pcs of all locals
pub struct CapabilityLocals<'tcx>(IndexVec<Local, CapabilityLocal<'tcx>>);

impl Debug for CapabilityLocals<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let v: Vec<_> = self.0.iter().filter(|c| !c.is_unallocated()).collect();
        v.fmt(f)
    }
}

impl<'tcx> CapabilityLocals<'tcx> {
    pub(crate) fn capability_projections(&self) -> Vec<&CapabilityProjections<'tcx>> {
        self.0
            .iter()
            .filter(|c| !c.is_unallocated())
            .map(|c| c.get_allocated())
            .collect()
    }

    pub fn default(local_count: usize) -> Self {
        Self(IndexVec::from_fn_n(
            |i| CapabilityLocal::Allocated(CapabilityProjections::new(i)),
            local_count,
        ))
    }

    pub fn empty() -> Self {
        Self(IndexVec::new())
    }
}
