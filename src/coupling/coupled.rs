use std::collections::BTreeSet;

use smallvec::SmallVec;

use crate::{
    pcg_validity_assert,
    utils::{display::DisplayWithCompilerCtxt, validity::HasValidityCheck, CompilerCtxt},
};

/// A collection of coupled PCG nodes. They will expire at the same time, and only one
/// node in the set will be alive.
///
/// These nodes are introduced for loops: place `a` may borrow from `b` or place
/// `b` may borrow from `a` depending on the number of loop iterations. Therefore,
/// `a` and `b` are coupled and only one can be accessed.
///
/// Internally, the nodes are stored in a `Vec` to allow for mutation
#[derive(Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Coupled<T>(SmallVec<[T; 4]>);

impl<T: Copy + Eq> Coupled<T> {
    pub(crate) fn retain(mut self, f: impl Fn(&T) -> bool) -> Option<Self> {
        self.0.retain(|x| f(x));
        if self.0.is_empty() {
            None
        } else {
            Some(self)
        }
    }

    pub(crate) fn all_elements_distinct(&self) -> bool {
        for (i, x) in self.0.iter().enumerate() {
            for y in self.0.iter().skip(i + 1) {
                if x == y {
                    return false;
                }
            }
        }
        true
    }

    pub(crate) fn is_disjoint(&self, other: &Self) -> bool {
        self.0.iter().all(|x| !other.0.contains(x))
    }

    pub(crate) fn empty() -> Self {
        Self(SmallVec::new())
    }

    pub(crate) fn insert(&mut self, item: T) {
        if !self.0.contains(&item) {
            self.0.push(item);
        }
    }

    pub(crate) fn merge(&mut self, other: &Self) {
        for item in other.0.iter() {
            self.insert(*item);
        }
    }

    pub(crate) fn mutate(&mut self, mut f: impl FnMut(&mut T)) {
        for item in self.0.iter_mut() {
            f(item);
        }
        pcg_validity_assert!(
            self.all_elements_distinct(),
            "Coupled elements are not distinct"
        );
    }
    pub(crate) fn singleton(item: T) -> Self {
        let mut coupled = Self::empty();
        coupled.insert(item);
        coupled
    }
}

impl<'tcx, T: HasValidityCheck<'tcx> + Copy + Eq> HasValidityCheck<'tcx> for Coupled<T> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        for t in self.0.iter() {
            t.check_validity(ctxt)?;
        }
        pcg_validity_assert!(
            self.all_elements_distinct(),
            "Coupled elements are not distinct"
        );
        Ok(())
    }
}

impl<'tcx, BC: Copy, T: DisplayWithCompilerCtxt<'tcx, BC>> DisplayWithCompilerCtxt<'tcx, BC>
    for Coupled<T>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        format!(
            "{{{}}}",
            self.0
                .iter()
                .map(|t| t.to_short_string(ctxt))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<T: Clone> Coupled<T> {
    pub(crate) fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }
}

impl<T> IntoIterator for Coupled<T> {
    type Item = T;
    type IntoIter = <SmallVec<[T; 4]> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T: Ord> Coupled<T> {
    pub(crate) fn contains(&self, item: &T) -> bool {
        self.0.contains(item)
    }
}

impl<T> From<BTreeSet<T>> for Coupled<T> {
    fn from(set: BTreeSet<T>) -> Self {
        Self(set.into_iter().collect())
    }
}

impl<T: Ord> From<Vec<T>> for Coupled<T> {
    fn from(vec: Vec<T>) -> Self {
        let mut bts = BTreeSet::new();
        for item in vec {
            bts.insert(item);
        }
        Self(bts.into_iter().collect())
    }
}
