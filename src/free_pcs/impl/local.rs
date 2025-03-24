// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    pcg_validity_assert,
    rustc_interface::{data_structures::fx::FxHashMap, middle::mir::Local},
};
use itertools::Itertools;

use crate::{
    combined_pcs::{PCGInternalError, PcgError},
    free_pcs::{CapabilityKind, RepackOp},
    utils::{corrected::CorrectedPlace, display::DisplayWithRepacker, Place, PlaceRepacker},
    validity_checks_enabled,
};

#[derive(Clone, PartialEq, Eq)]
/// The permissions of a local, each key in the hashmap is a "root" projection of the local
/// Examples of root projections are: `_1`, `*_1.f`, `*(*_.f).g` (i.e. either a local or a deref)
pub enum CapabilityLocal<'tcx> {
    Unallocated,
    Allocated(CapabilityProjections<'tcx>),
}

impl Debug for CapabilityLocal<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Unallocated => write!(f, "U"),
            Self::Allocated(cps) => write!(f, "{cps:?}"),
        }
    }
}

impl<'tcx> CapabilityLocal<'tcx> {
    pub(crate) fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        match self {
            Self::Unallocated => vec![],
            Self::Allocated(cps) => cps.debug_lines(repacker),
        }
    }

    pub fn get_allocated(&self) -> &CapabilityProjections<'tcx> {
        match self {
            Self::Allocated(cps) => cps,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }
    pub fn get_allocated_mut(&mut self) -> &mut CapabilityProjections<'tcx> {
        match self {
            Self::Allocated(cps) => cps,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }
    pub fn new(local: Local, perm: CapabilityKind) -> Self {
        Self::Allocated(CapabilityProjections::new(local, perm))
    }
    pub fn is_unallocated(&self) -> bool {
        matches!(self, Self::Unallocated)
    }
}

pub trait CheckValidityOnExpiry {
    fn check_validity_on_expiry(&self);
}

pub struct DropGuard<'a, S: CheckValidityOnExpiry, T> {
    source: *const S,
    value: &'a mut T,
}

impl<S: CheckValidityOnExpiry, T> std::ops::Deref for DropGuard<'_, S, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.value
    }
}

impl<S: CheckValidityOnExpiry, T> std::ops::DerefMut for DropGuard<'_, S, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.value
    }
}

impl<'a, S: CheckValidityOnExpiry, T> DropGuard<'a, S, T> {
    /// Caller must ensure that value borrows from `source`
    #[allow(dead_code)]
    pub(crate) unsafe fn new(source: *const S, value: &'a mut T) -> Self {
        Self { source, value }
    }
}

impl<S: CheckValidityOnExpiry, T> Drop for DropGuard<'_, S, T> {
    fn drop(&mut self) {
        // SAFETY: DropGuard::new ensures that `value` mutably borrows from `source`
        // once the DropGuard is dropped, `source` will no longer have any mutable references
        // and we can safely obtain a shared reference to it
        unsafe { (*self.source).check_validity_on_expiry() };
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CapabilityProjections<'tcx> {
    local: Local,
    expansions: FxHashMap<Place<'tcx>, PlaceExpansion<'tcx>>,
    capabilities: FxHashMap<Place<'tcx>, CapabilityKind>,
}

impl CheckValidityOnExpiry for CapabilityProjections<'_> {
    fn check_validity_on_expiry(&self) {}
}

impl<'tcx> CapabilityProjections<'tcx> {
    pub(crate) fn insert_expansion(&mut self, place: Place<'tcx>, expansion: PlaceExpansion<'tcx>) {
        self.expansions.insert(place, expansion);
    }

    pub(crate) fn expansions(&self) -> &FxHashMap<Place<'tcx>, PlaceExpansion<'tcx>> {
        &self.expansions
    }

    pub(crate) fn leaves(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<Place<'tcx>> {
        self.expansions
            .iter()
            .flat_map(|(p, e)| p.expansion_places(e, repacker))
            .filter(|p| !self.contains_expansion_from(*p))
            .collect::<Vec<_>>()
    }

    pub(crate) fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.capabilities
            .iter()
            .map(|(p, k)| format!("{}: {:?}", p.to_short_string(repacker), k))
            .collect()
    }

    pub fn new(local: Local, perm: CapabilityKind) -> Self {
        Self {
            local,
            expansions: FxHashMap::default(),
            capabilities: FxHashMap::from_iter([(local.into(), perm)]),
        }
    }
    pub fn new_uninit(local: Local) -> Self {
        Self::new(local, CapabilityKind::Write)
    }

    pub(crate) fn contains_expansion_from(&self, place: Place<'tcx>) -> bool {
        self.expansions.contains_key(&place)
    }

    pub(crate) fn contains_expansion_to(
        &self,
        place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        match place.last_projection() {
            Some((p, _)) => {
                if let Some(expansion) = self.expansions.get(&p) {
                    p.expansion_places(expansion, repacker).contains(&place)
                } else {
                    false
                }
            }
            None => place.local == self.local,
        }
    }

    pub(crate) fn get_local(&self) -> Local {
        self.local
    }

    pub(crate) fn set_capability(
        &mut self,
        place: Place<'tcx>,
        cap: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        pcg_validity_assert!(
            place.is_owned(repacker),
            "Setting capability for non-owned place {}",
            place.to_short_string(repacker)
        );
        self.capabilities.insert(place, cap);
    }

    pub(crate) fn remove_capability(&mut self, place: Place<'tcx>) -> Option<CapabilityKind> {
        self.capabilities.remove(&place)
    }

    pub(crate) fn get_capability(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        self.capabilities.get(&place).copied()
    }

    pub(crate) fn place_capabilities_mut(&mut self) -> &mut FxHashMap<Place<'tcx>, CapabilityKind> {
        &mut self.capabilities
    }

    pub fn place_capabilities(&self) -> &FxHashMap<Place<'tcx>, CapabilityKind> {
        &self.capabilities
    }

    fn check_validity(&self) {}

    pub(crate) fn expand(
        &mut self,
        from: Place<'tcx>,
        to: CorrectedPlace<'tcx>,
        for_cap: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        tracing::debug!("Expanding to {:?}", *to);
        assert!(
            to.is_owned(repacker),
            "Expanding to borrowed place {:?}",
            *to
        );

        tracing::debug!("Expanding from {:?} to {:?} for {:?}", from, *to, for_cap);

        let from_cap = if let Some(cap) = self.get_capability(from) {
            cap
        } else {
            let err = format!("No capability for {}", from.to_short_string(repacker));
            tracing::error!("{}", err);
            return Err(PcgError::internal(err));
        };
        let expansion = from.expand(*to, repacker)?;

        // Update permission of `from` place
        let projection_path_perm = if for_cap.is_read() {
            Some(CapabilityKind::Read)
        } else {
            None
        };

        for place in expansion.other_expansions() {
            self.set_capability(place, for_cap, repacker);
        }

        let mut ops = Vec::new();

        for expansion in expansion.expansions() {
            self.insert_expansion(
                expansion.base_place(),
                PlaceExpansion::from_places(expansion.expansion(), repacker),
            );
            if let Some(perm) = projection_path_perm {
                self.set_capability(expansion.base_place(), perm, repacker);
            } else {
                self.remove_capability(expansion.base_place());
            }
            if expansion.kind.is_box() && from_cap.is_shallow_exclusive() {
                ops.push(RepackOp::DerefShallowInit(
                    expansion.base_place(),
                    expansion.target_place,
                ));
            } else {
                ops.push(RepackOp::expand(
                    expansion.base_place(),
                    expansion.target_place,
                    for_cap,
                    repacker,
                ));
            }
        }

        self.set_capability(*to, for_cap, repacker);

        if validity_checks_enabled() {
            self.check_validity();
        }

        Ok(ops)
    }

    // TODO: this could be implemented more efficiently, by assuming that a valid
    // state can always be packed up to the root
    pub(crate) fn collapse(
        &mut self,
        to: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PCGInternalError> {
        let expansions = self
            .expansions
            .iter()
            .filter(|(p, _)| to.is_prefix(**p))
            .map(|(p, e)| (*p, e.clone()))
            .sorted_by_key(|(p, _)| p.projection.len())
            .rev()
            .collect::<Vec<_>>();
        let ops = expansions
            .into_iter()
            .map(|(p, expansion)| {
                let expansion_places = p.expansion_places(&expansion, repacker);
                let retained_cap = expansion_places.iter().fold(
                    CapabilityKind::Exclusive,
                    |acc, place| match self.remove_capability(*place) {
                        Some(cap) => acc.minimum(cap).unwrap_or(CapabilityKind::Write),
                        None => acc,
                    },
                );
                self.set_capability(p, retained_cap, repacker);
                self.expansions.remove(&p);
                RepackOp::Collapse(p, expansion_places[0], retained_cap)
            })
            .collect();
        if validity_checks_enabled() {
            self.check_validity();
        }
        Ok(ops)
    }
}
