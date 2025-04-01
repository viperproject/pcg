// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    fmt::{Debug, Formatter, Result},
    rc::Rc,
};

use crate::rustc_interface::{
    index::{Idx, IndexVec},
    middle::mir::{Local, RETURN_PLACE},
    mir_dataflow::fmt::DebugWithContext,
};
use derive_more::{Deref, DerefMut};

use super::{engine::FpcsEngine, CapabilityKind};
use crate::{
    pcg::EvalStmtPhase,
    free_pcs::{CapabilityLocal, CapabilityProjections},
    utils::{domain_data::DomainData, PlaceRepacker},
};

#[derive(Clone)]
pub struct FreePlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
    pub(crate) data: DomainData<Option<CapabilityLocals<'tcx>>>,
}
impl<'a, 'tcx> FreePlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) fn new(repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            repacker,
            data: DomainData::default(),
        }
    }

    pub fn initialize_as_start_block(&mut self) {
        let always_live = self.repacker.always_live_locals();
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(self.repacker.body().arg_count);
        let capability_summary = IndexVec::from_fn_n(
            |local| {
                if local == return_local {
                    // Return local is allocated but uninitialized
                    CapabilityLocal::new(local, CapabilityKind::Write)
                } else if local <= last_arg {
                    // Arguments are allocated and initialized
                    CapabilityLocal::new(local, CapabilityKind::Exclusive)
                } else if always_live.contains(local) {
                    // Always live locals start allocated but uninitialized
                    CapabilityLocal::new(local, CapabilityKind::Write)
                } else {
                    // Other locals are unallocated
                    CapabilityLocal::Unallocated
                }
            },
            self.repacker.local_count(),
        );
        self.data.entry_state = Rc::new(Some(CapabilityLocals(capability_summary)));
        self.data.states.0.post_main = self.data.entry_state.clone();
    }
}

impl PartialEq for FreePlaceCapabilitySummary<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.data.states[EvalStmtPhase::PostMain] == other.data.states[EvalStmtPhase::PostMain]
    }
}
impl Eq for FreePlaceCapabilitySummary<'_, '_> {}

impl Debug for FreePlaceCapabilitySummary<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.data.states[EvalStmtPhase::PostMain].fmt(f)
    }
}
impl<'a, 'tcx> DebugWithContext<FpcsEngine<'a, 'tcx>> for FreePlaceCapabilitySummary<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        _old: &Self,
        _ctxt: &FpcsEngine<'a, 'tcx>,
        _f: &mut Formatter<'_>,
    ) -> Result {
        todo!()
    }
}

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The free pcs of all locals
pub struct CapabilityLocals<'tcx>(IndexVec<Local, CapabilityLocal<'tcx>>);

// impl Default for CapabilitySummary<'_> {
//     fn default() -> Self {
//         Self::empty()
//     }
// }

impl Debug for CapabilityLocals<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let v: Vec<_> = self.0.iter().filter(|c| !c.is_unallocated()).collect();
        v.fmt(f)
    }
}

impl<'tcx> CapabilityLocals<'tcx> {

    pub(crate) fn capability_projections_mut(&mut self) -> Vec<&mut CapabilityProjections<'tcx>> {
        self.0
            .iter_mut()
            .filter(|c| !c.is_unallocated())
            .map(|c| c.get_allocated_mut())
            .collect()
    }

    pub(crate) fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.0
            .iter()
            .map(|c| c.debug_lines(repacker))
            .collect::<Vec<_>>()
            .concat()
    }

    pub fn default(local_count: usize) -> Self {
        Self(IndexVec::from_fn_n(
            |i| {
                CapabilityLocal::Allocated(CapabilityProjections::new(i, CapabilityKind::Exclusive))
            },
            local_count,
        ))
    }

    pub fn empty() -> Self {
        Self(IndexVec::new())
    }
}
