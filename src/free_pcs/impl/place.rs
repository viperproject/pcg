// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use derive_more::Deref;
use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
};

use rustc_interface::data_structures::fx::FxHashSet;

use crate::{rustc_interface, utils::Place};

#[derive(Debug, Deref)]
pub(crate) struct RelatedSet<'tcx>(FxHashSet<(Place<'tcx>, CapabilityKind)>);

impl<'tcx> RelatedSet<'tcx> {
    pub fn new(related: FxHashSet<(Place<'tcx>, CapabilityKind)>) -> Self {
        Self(related)
    }
    pub fn get_places(&self) -> FxHashSet<Place<'tcx>> {
        self.0.iter().map(|(p, _)| *p).collect()
    }
    pub fn get_only_place(&self) -> Place<'tcx> {
        assert_eq!(self.0.len(), 1);
        self.0.iter().next().unwrap().0
    }
    pub fn common_prefix(&self, to: Place<'tcx>) -> Place<'tcx> {
        self.get_places()
            .iter()
            .fold(to, |acc, p| acc.common_prefix(*p))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum CapabilityKind {
    /// An immutable owned place, or a shared borrow
    Read,

    /// For owned places, this capability is used when the place is moved out
    /// of. This capability is used for both owned and borrowed places just before
    /// they are overwritten.
    Write,

    /// Writes and reads are permitted to this place, and the place is not
    /// borrowed.
    Exclusive,

    /// This place is mutably borrowed.
    Lent,

    /// There are outstanding shared borrows to this place or to projections of
    /// this place. The capability to the place can be restored to
    /// [`CapabilityKind::Exclusive`] in exchange for the capabilities of its
    /// projections when the borrows expire.
    LentShared,

    /// [`CapabilityKind::Exclusive`] for everything not through a dereference,
    /// [`CapabilityKind::Write`] for everything through a dereference.
    ShallowExclusive,
}
impl Debug for CapabilityKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            CapabilityKind::Read => write!(f, "R"),
            CapabilityKind::Write => write!(f, "W"),
            CapabilityKind::Exclusive => write!(f, "E"),
            CapabilityKind::ShallowExclusive => write!(f, "e"),
            CapabilityKind::Lent => write!(f, "L"),
            CapabilityKind::LentShared => write!(f, "Ls"),
        }
    }
}

impl PartialOrd for CapabilityKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        match (self, other) {
            (CapabilityKind::Write, _) | (_, CapabilityKind::Exclusive) => Some(Ordering::Less),
            (CapabilityKind::Exclusive, _) | (_, CapabilityKind::Write) => Some(Ordering::Greater),
            (CapabilityKind::Read, _) | (_, CapabilityKind::Lent) => Some(Ordering::Less),
            (CapabilityKind::Lent, _) | (_, CapabilityKind::Read) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl CapabilityKind {
    pub fn is_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Exclusive)
    }
    pub fn is_lent_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Lent)
    }
    pub fn is_read(self) -> bool {
        matches!(self, CapabilityKind::Read)
    }
    pub fn is_write(self) -> bool {
        matches!(self, CapabilityKind::Write)
    }
    pub fn is_shallow_exclusive(self) -> bool {
        matches!(self, CapabilityKind::ShallowExclusive)
    }
    pub fn minimum(self, other: Self) -> Option<Self> {
        match self.partial_cmp(&other)? {
            Ordering::Greater => Some(other),
            _ => Some(self),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_capability_kind_partial_order() {
        // Get all variants of CapabilityKind
        let variants = [
            CapabilityKind::Read,
            CapabilityKind::Write,
            CapabilityKind::Exclusive,
            CapabilityKind::Lent,
            CapabilityKind::LentShared,
            CapabilityKind::ShallowExclusive,
        ];

        // Test reflexivity: a ≤ a for all a
        for &a in &variants {
            assert_eq!(
                Some(Ordering::Equal),
                a.partial_cmp(&a),
                "Reflexivity failed for {:?}",
                a
            );
        }

        // Test antisymmetry: if a ≤ b and b ≤ a then a = b
        for &a in &variants {
            for &b in &variants {
                if let (Some(ord1), Some(ord2)) = (a.partial_cmp(&b), b.partial_cmp(&a)) {
                    if ord1 != Ordering::Greater && ord2 != Ordering::Greater {
                        assert_eq!(
                            a, b,
                            "Antisymmetry failed: {:?} and {:?} form a cycle but are not equal",
                            a, b
                        );
                    }
                }
            }
        }

        // Test transitivity: if a ≤ b and b ≤ c then a ≤ c
        for &a in &variants {
            for &b in &variants {
                for &c in &variants {
                    if let (Some(ord1), Some(ord2)) = (a.partial_cmp(&b), b.partial_cmp(&c)) {
                        if ord1 != Ordering::Greater && ord2 != Ordering::Greater {
                            assert!(
                                matches!(a.partial_cmp(&c), Some(ord) if ord != Ordering::Greater),
                                "Transitivity failed: {:?} ≤ {:?} and {:?} ≤ {:?}, but {:?} ≰ {:?}",
                                a,
                                b,
                                b,
                                c,
                                a,
                                c
                            );
                        }
                    }
                }
            }
        }

        // Verify specific known relationships from the implementation
        assert!(matches!(
            CapabilityKind::Write.partial_cmp(&CapabilityKind::Exclusive),
            Some(Ordering::Less)
        ));
        assert!(matches!(
            CapabilityKind::Read.partial_cmp(&CapabilityKind::Lent),
            Some(Ordering::Less)
        ));
    }
}
