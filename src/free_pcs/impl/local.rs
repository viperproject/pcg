// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use derive_more::Deref;
use rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::mir::Local,
};

use crate::{
    combined_pcs::{PCGError, PCGInternalError},
    free_pcs::{CapabilityKind, RelatedSet, RepackOp},
    pcg_validity_assert, rustc_interface,
    utils::{
        corrected::CorrectedPlace, display::DisplayWithRepacker, ExpandStep, Place, PlaceOrdering,
        PlaceRepacker,
    },
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

impl Default for CapabilityLocal<'_> {
    fn default() -> Self {
        Self::Allocated(CapabilityProjections::empty())
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

impl<'a, 'tcx, S: CheckValidityOnExpiry, T> std::ops::Deref for DropGuard<'a, S, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.value
    }
}

impl<'a, 'tcx, S: CheckValidityOnExpiry, T> std::ops::DerefMut for DropGuard<'a, S, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.value
    }
}

impl<'a, 'tcx, S: CheckValidityOnExpiry, T> DropGuard<'a, S, T> {
    /// Caller must ensure that value borrows from `source`
    pub(crate) unsafe fn new(source: *const S, value: &'a mut T) -> Self {
        Self { source, value }
    }
}

impl<'a, 'tcx, S: CheckValidityOnExpiry, T> Drop for DropGuard<'a, S, T> {
    fn drop(&mut self) {
        // SAFETY: DropGuard::new ensures that `value` mutably borrows from `source`
        // once the DropGuard is dropped, `source` will no longer have any mutable references
        // and we can safely obtain a shared reference to it
        unsafe { (*self.source).check_validity_on_expiry() };
    }
}

#[derive(Clone, PartialEq, Eq, Deref)]
/// The permissions for all the projections of a place
// We only need the projection part of the place
pub struct CapabilityProjections<'tcx>(FxHashMap<Place<'tcx>, CapabilityKind>);

impl Debug for CapabilityProjections<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.0.fmt(f)
    }
}

impl<'tcx> CheckValidityOnExpiry for CapabilityProjections<'tcx> {
    fn check_validity_on_expiry(&self) {
        self.check_validity();
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    pub(crate) fn is_leaf(&self, place: Place<'tcx>) -> bool {
        self.0.iter().all(|(p, _)| p.is_prefix(place))
    }

    pub(crate) fn get_mut(&mut self, place: Place<'tcx>) -> Option<&mut CapabilityKind> {
        self.0.get_mut(&place)
    }

    pub(crate) fn insert(&mut self, place: Place<'tcx>, cap: CapabilityKind) {
        self.0.insert(place, cap);
    }

    pub(crate) fn extend(
        &mut self,
        other: impl IntoIterator<Item = (Place<'tcx>, CapabilityKind)>,
    ) {
        self.0.extend(other);
        if validity_checks_enabled() {
            self.check_validity();
        }
    }

    pub(crate) fn remove(&mut self, place: &Place<'tcx>) -> Option<CapabilityKind> {
        self.0.remove(place)
    }

    pub(crate) fn iter_mut<'a>(
        &'a mut self,
    ) -> impl Iterator<
        Item = (
            Place<'tcx>,
            DropGuard<'a, CapabilityProjections<'tcx>, CapabilityKind>,
        ),
    > {
        struct Iter<'a, 'tcx> {
            inner: *mut CapabilityProjections<'tcx>,
            places: Vec<Place<'tcx>>,
            idx: usize,
            _marker: std::marker::PhantomData<&'a ()>,
        }

        impl<'a, 'tcx: 'a> Iterator for Iter<'a, 'tcx> {
            type Item = (
                Place<'tcx>,
                DropGuard<'a, CapabilityProjections<'tcx>, CapabilityKind>,
            );

            fn next(&mut self) -> Option<Self::Item> {
                if self.idx >= self.places.len() {
                    None
                } else {
                    let place: Place<'tcx> = self.places[self.idx];
                    // SAFETY: As long as `Iter<'a, tcx> is live, self.inner is blocked`
                    let capability: &'a mut CapabilityKind =
                        unsafe { self.inner.as_mut().unwrap().get_mut(place).unwrap() };
                    self.idx += 1;
                    // SAFETY: `capability` borrows from self.inner
                    let guard = unsafe { DropGuard::new(self.inner, capability) };
                    Some((place, guard))
                }
            }
        }

        let places = self.0.keys().copied().collect();
        Iter {
            inner: self,
            places,
            idx: 0,
            _marker: std::marker::PhantomData,
        }
    }

    fn check_validity(&self) {
        for (place, cap) in &**self {
            if cap.is_exclusive() {
                for (other_place, other_cap) in &**self {
                    if other_place.is_strict_prefix(*place) && other_cap.is_exclusive() {
                        panic!(
                            "Found place {:?} with Exclusive capability that has a prefix {:?} also with Exclusive capability",
                            place,
                            other_place
                    );
                    }
                }
            }
        }
    }
    pub(crate) fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.iter()
            .map(|(p, k)| format!("{}: {:?}", p.to_short_string(repacker), k))
            .collect()
    }

    pub fn new(local: Local, perm: CapabilityKind) -> Self {
        Self([(local.into(), perm)].into_iter().collect())
    }
    pub fn new_uninit(local: Local) -> Self {
        Self::new(local, CapabilityKind::Write)
    }
    /// Should only be called when creating an update within `ModifiesFreeState`
    pub(crate) fn empty() -> Self {
        Self(FxHashMap::default())
    }

    pub(crate) fn get_local(&self) -> Local {
        self.iter().next().unwrap().0.local
    }

    pub(crate) fn update_cap(&mut self, place: Place<'tcx>, cap: CapabilityKind) {
        let _old = self.insert(place, cap);
        if validity_checks_enabled() {
            self.check_validity();
        }
        // assert!(old.is_some());
    }

    /// Returns all related projections of the given place that are contained in this map.
    /// A `Ordering::Less` means that the given `place` is a prefix of the iterator place.
    /// For example: find_all_related(x.f.g) = [(Less, x.f.g.h), (Greater, x.f)]
    /// It also checks that the ordering conforms to the expected ordering (the above would
    /// fail in any situation since all orderings need to be the same)
    pub(crate) fn find_all_related(
        &self,
        to: Place<'tcx>,
        mut expected: Option<PlaceOrdering>,
    ) -> RelatedSet<'tcx> {
        // let mut minimum = None::<CapabilityKind>;
        let mut related = Vec::new();
        for (&from, &cap) in &**self {
            if let Some(ord) = from.partial_cmp(to) {
                // let cap_no_read = cap.read_as_exclusive();
                // minimum = if let Some(min) = minimum {
                //     Some(min.minimum(cap_no_read).unwrap())
                // } else {
                //     Some(cap_no_read)
                // };
                if let Some(_expected) = expected {
                    // assert_eq!(ord, expected, "({self:?}) {from:?} {to:?}");
                } else {
                    expected = Some(ord);
                }
                related.push((from, cap));
            }
        }
        assert!(
            !related.is_empty(),
            "Cannot find related of {to:?} in {self:?}"
        );
        let relation = expected.unwrap();
        if matches!(relation, PlaceOrdering::Prefix | PlaceOrdering::Equal) {
            // assert_eq!(related.len(), 1);
        }
        RelatedSet::new(related.into_iter().collect())
    }

    pub(crate) fn expand(
        &mut self,
        from: Place<'tcx>,
        to: CorrectedPlace<'tcx>,
        for_cap: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PCGError> {
        assert!(
            !from.is_mut_ref(repacker.body(), repacker.tcx()),
            "Mutable reference {:?} should be expanded in borrow PCG, not owned PCG",
            from
        );
        pcg_validity_assert!(
            !self.contains_key(&to),
            "We don't need to expand to {} because it already has a capability ({:?})",
            to.to_short_string(repacker),
            self.get(&to)
        );

        let (expand_steps, other_expanded_places) = from.expand(*to, repacker)?;

        // Update permission of `from` place
        let from_cap = *self.get(&from).unwrap();
        let other_place_perm = from_cap;
        let projection_path_perm = if for_cap.is_read() {
            Some(CapabilityKind::Read)
        } else {
            None
        };

        for place in other_expanded_places.iter() {
            self.insert(*place, other_place_perm);
        }

        let mut ops = Vec::new();

        for ExpandStep {
            base_place,
            projected_place,
            kind,
        } in expand_steps
        {
            if let Some(perm) = projection_path_perm {
                self.insert(base_place, perm);
            } else {
                self.remove(&base_place);
            }

            if kind.is_box() && from_cap.is_shallow_exclusive() {
                ops.push(RepackOp::DerefShallowInit(base_place, projected_place));
            } else {
                ops.push(RepackOp::Expand(base_place, projected_place, for_cap));
            }
        }

        self.insert(*to, from_cap);

        if validity_checks_enabled() {
            self.check_validity();
        }

        Ok(ops)
    }

    // TODO: this could be implemented more efficiently, by assuming that a valid
    // state can always be packed up to the root
    pub(crate) fn collapse(
        &mut self,
        from: FxHashSet<Place<'tcx>>,
        to: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PCGInternalError> {
        let f = from.clone();
        let mut old_caps: FxHashMap<_, _> = from
            .iter()
            .flat_map(|&p| self.remove(&p).map(|cap| (p, cap)))
            .collect();
        let collapsed = to.collapse(from, repacker);
        eprintln!(
            "Collapsing to {} from {} requires {:?}",
            to.to_short_string(repacker),
            f.iter()
                .map(|p| p.to_short_string(repacker))
                .collect::<Vec<_>>()
                .join(", "),
            collapsed
        );
        let mut exclusive_at = Vec::new();
        if !to.projects_shared_ref(repacker) {
            for ExpandStep {
                projected_place: to,
                kind,
                ..
            } in &collapsed
            {
                if kind.is_shared_ref() {
                    let mut is_prefixed = false;
                    exclusive_at
                        .extract_if(|old| {
                            let cmp = to.either_prefix(*old);
                            if matches!(cmp, Some(false)) {
                                is_prefixed = true;
                            }
                            cmp.unwrap_or_default()
                        })
                        .for_each(drop);
                    if !is_prefixed {
                        exclusive_at.push(*to);
                    }
                }
            }
        }
        let mut ops = Vec::new();
        for ExpandStep {
            base_place,
            projected_place,
            ..
        } in &collapsed
        {
            let removed_perms: Vec<_> = old_caps
                .extract_if(|old, _| projected_place.is_prefix(*old))
                .collect();
            let perm = removed_perms
                .iter()
                .fold(CapabilityKind::Exclusive, |acc, (_, p)| {
                    acc.minimum(*p).unwrap_or_else(|| {
                        panic!("Minimum of {:?}", removed_perms);
                    })
                });
            for (from, from_perm) in removed_perms {
                match from_perm.partial_cmp(&perm) {
                    Some(std::cmp::Ordering::Equal) => {} // Equal, do nothing
                    Some(std::cmp::Ordering::Greater) => {
                        ops.push(RepackOp::Weaken(from, from_perm, perm));
                    }
                    _ => panic!("Weaken {:?} {:?} {:?}", from, from_perm, perm),
                }
            }
            old_caps.insert(*base_place, perm);
            ops.push(RepackOp::Collapse(*base_place, *projected_place, perm));
        }
        pcg_validity_assert!(
            old_caps.contains_key(&to),
            "Old capabilities does not have a capability for collapse target {}",
            to.to_short_string(repacker)
        );
        self.insert(to, old_caps[&to]);
        if validity_checks_enabled() {
            self.check_validity();
        }
        Ok(ops)
    }
}
