use itertools::Itertools;

use crate::{
    borrow_checker::BorrowCheckerInterface,
    pcg_validity_assert,
    utils::{CompilerCtxt, display::DisplayWithCompilerCtxt},
    validity_checks_enabled,
};

#[allow(unused)]
pub(crate) trait IterExt<T: Copy + std::fmt::Debug>: Iterator<Item = T> {
    fn find_zero_or_one<'tcx>(&mut self, f: impl Fn(&T) -> bool) -> Option<T>
    where
        Self: Sized,
    {
        if validity_checks_enabled() {
            let results = self.filter(f).collect::<Vec<_>>();
            pcg_validity_assert!(
                results.len() <= 1,
                "Found multiple items in iterator: {:?}",
                results.iter().map(|t| format!("{t:?}")).join(", ")
            );
            results.first().copied()
        } else {
            self.find(f)
        }
    }
}

impl<T: Copy + std::fmt::Debug, It: Iterator<Item = T>> IterExt<T> for It {}
