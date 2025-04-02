// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    pcg::place_capabilities::PlaceCapabilities,
    rustc_interface::{data_structures::fx::FxHashMap, middle::mir::Local},
};
use itertools::Itertools;

use crate::{
    free_pcs::{CapabilityKind, RepackOp},
    pcg::{PCGInternalError, PcgError},
    utils::{corrected::CorrectedPlace, display::DisplayWithRepacker, Place, PlaceRepacker},
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
    pub fn new(local: Local) -> Self {
        Self::Allocated(CapabilityProjections::new(local))
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
        if self.expansions.is_empty() {
            return vec![self.local.into()];
        }
        self.expansions
            .iter()
            .flat_map(|(p, e)| p.expansion_places(e, repacker))
            .filter(|p| !self.contains_expansion_from(*p))
            .collect::<Vec<_>>()
    }

    pub fn new(local: Local) -> Self {
        Self {
            local,
            expansions: FxHashMap::default(),
        }
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

    pub(crate) fn expand(
        &mut self,
        from: Place<'tcx>,
        to: CorrectedPlace<'tcx>,
        for_cap: CapabilityKind,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        assert!(
            to.is_owned(repacker),
            "Expanding to borrowed place {:?}",
            *to
        );

        tracing::debug!("Expanding from {:?} to {:?} for {:?}", from, *to, for_cap);

        let from_cap = if let Some(cap) = capabilities.get(from.into()) {
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
            capabilities.insert(place.into(), for_cap);
        }

        let mut ops = Vec::new();

        for expansion in expansion.expansions() {
            self.insert_expansion(
                expansion.base_place(),
                PlaceExpansion::from_places(expansion.expansion(), repacker),
            );
            if let Some(perm) = projection_path_perm {
                capabilities.insert(expansion.base_place().into(), perm);
            } else {
                capabilities.remove(expansion.base_place().into());
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

        capabilities.insert((*to).into(), for_cap);

        Ok(ops)
    }

    // TODO: this could be implemented more efficiently, by assuming that a valid
    // state can always be packed up to the root
    pub(crate) fn collapse(
        &mut self,
        to: Place<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
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
                let retained_cap =
                    expansion_places
                        .iter()
                        .fold(CapabilityKind::Exclusive, |acc, place| {
                            match capabilities.remove((*place).into()) {
                                Some(cap) => acc.minimum(cap).unwrap_or(CapabilityKind::Write),
                                None => acc,
                            }
                        });
                capabilities.insert(p.into(), retained_cap);
                self.expansions.remove(&p);
                RepackOp::Collapse(p, expansion_places[0], retained_cap)
            })
            .collect();
        Ok(ops)
    }
}
