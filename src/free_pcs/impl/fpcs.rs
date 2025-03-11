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
    combined_pcs::{EvalStmtPhase, PcgError},
    free_pcs::{CapabilityLocal, CapabilityProjections, RepackOp},
    utils::{domain_data::DomainData, eval_stmt_data::EvalStmtData, PlaceRepacker},
};

pub(crate) struct RepackOps<'tcx> {
    pub(crate) start: Vec<RepackOp<'tcx>>,
    pub(crate) middle: Vec<RepackOp<'tcx>>,
}

#[derive(Clone)]
pub struct FreePlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
    pub(crate) data: DomainData<CapabilitySummary<'tcx>>,
    pub(crate) actions: EvalStmtData<Vec<RepackOp<'tcx>>>,
}
impl<'a, 'tcx> FreePlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) fn new(
        repacker: PlaceRepacker<'a, 'tcx>,
        capability_summary: Rc<CapabilitySummary<'tcx>>,
    ) -> Self {
        Self {
            repacker,
            data: DomainData::new(capability_summary),
            actions: EvalStmtData::default(),
        }
    }

    pub fn initialize_as_start_block(&mut self) {
        let always_live = self.repacker.always_live_locals();
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(self.repacker.body().arg_count);
        let entry_state = Rc::<_>::make_mut(&mut self.data.entry_state);
        for (local, cap) in entry_state.iter_enumerated_mut() {
            let new_cap = if local == return_local {
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
            };
            *cap = new_cap;
        }
    }

    pub(crate) fn repack_ops(&self) -> std::result::Result<RepackOps<'tcx>, PcgError> {
        let start = self.actions[EvalStmtPhase::PreOperands].clone();
        let middle = self.actions[EvalStmtPhase::PreMain].clone();
        Ok(RepackOps { start, middle })
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
        old: &Self,
        _ctxt: &FpcsEngine<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        let RepackOps { start, middle } = self.repack_ops().unwrap();
        if !start.is_empty() {
            writeln!(f, "{start:?}")?;
        }
        CapabilitySummaryCompare(
            &self.data.states[EvalStmtPhase::PreOperands],
            &old.data.states[EvalStmtPhase::PostMain],
            "",
        )
        .fmt(f)?;
        CapabilitySummaryCompare(
            &self.data.states[EvalStmtPhase::PostOperands],
            &self.data.states[EvalStmtPhase::PreOperands],
            "ARGUMENTS:\n",
        )
        .fmt(f)?;
        if !middle.is_empty() {
            writeln!(f, "{middle:?}")?;
        }
        CapabilitySummaryCompare(
            &self.data.states[EvalStmtPhase::PreMain],
            &self.data.states[EvalStmtPhase::PostOperands],
            "",
        )
        .fmt(f)?;
        CapabilitySummaryCompare(
            &self.data.states[EvalStmtPhase::PostMain],
            &self.data.states[EvalStmtPhase::PreMain],
            "STATEMENT:\n",
        )
        .fmt(f)?;
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The free pcs of all locals
pub struct CapabilitySummary<'tcx>(IndexVec<Local, CapabilityLocal<'tcx>>);

// impl Default for CapabilitySummary<'_> {
//     fn default() -> Self {
//         Self::empty()
//     }
// }

impl Debug for CapabilitySummary<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let v: Vec<_> = self.0.iter().filter(|c| !c.is_unallocated()).collect();
        v.fmt(f)
    }
}

impl<'tcx> CapabilitySummary<'tcx> {
    pub(crate) fn capability_projections(&mut self) -> Vec<&mut CapabilityProjections<'tcx>> {
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

struct CapabilitySummaryCompare<'a, 'tcx>(
    &'a CapabilitySummary<'tcx>,
    &'a CapabilitySummary<'tcx>,
    &'a str,
);
impl Debug for CapabilitySummaryCompare<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.0 == self.1 {
            return Ok(());
        }
        write!(f, "{}", self.2)?;
        for (new, old) in self.0.iter().zip(self.1.iter()) {
            let changed = match (new, old) {
                (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => false,
                (CapabilityLocal::Unallocated, CapabilityLocal::Allocated(a)) => {
                    write!(f, "\u{001f}-{:?}", a.get_local())?;
                    true
                }
                (CapabilityLocal::Allocated(a), CapabilityLocal::Unallocated) => {
                    write!(f, "\u{001f}+{:?}", a.get_local())?;
                    true
                }
                (CapabilityLocal::Allocated(_), CapabilityLocal::Allocated(_)) => {
                    true
                    // if new != old {
                    //     let mut new_set = CapabilityProjections::empty();
                    //     let mut old_set = CapabilityProjections::empty();
                    //     for (&p, &nk) in new.iter() {
                    //         match old.get(&p) {
                    //             Some(&ok) if nk == ok => (),
                    //             _ => {
                    //                 new_set.insert(p, nk);
                    //             }
                    //         }
                    //     }
                    //     for (&p, &ok) in old.iter() {
                    //         match new.get(&p) {
                    //             Some(&nk) if nk == ok => (),
                    //             _ => {
                    //                 old_set.insert(p, ok);
                    //             }
                    //         }
                    //     }
                    //     if !old_set.is_empty() {
                    //         write!(f, "\u{001f}-{old_set:?}")?
                    //     }
                    //     if !new_set.is_empty() {
                    //         write!(f, "\u{001f}+{new_set:?}")?
                    //     }
                    //     true
                    // } else {
                    //     false
                    // }
                }
            };
            if changed {
                write!(f, "</font><font color=\"black\">")?;
                if f.alternate() {
                    writeln!(f)?;
                } else {
                    write!(f, "\t")?;
                }
            }
        }
        Ok(())
    }
}
