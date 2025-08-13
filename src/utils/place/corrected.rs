use crate::rustc_interface::middle::mir;
use crate::utils::{HasCompilerCtxt, Place};
use derive_more::{Deref, DerefMut};

impl<'tcx> CorrectedPlace<'tcx> {
    pub fn new<'a>(place: Place<'tcx>, repacker: impl HasCompilerCtxt<'a, 'tcx>) -> Self
    where
        'tcx: 'a,
    {
        Self(place.with_inherent_region(repacker))
    }

    pub(crate) fn last_projection(&self) -> Option<CorrectedPlaceElem<'tcx>> {
        self.0
            .last_projection()
            .map(|(_, elem)| CorrectedPlaceElem(elem))
    }
}

/// A place element obtained from a [`CorrectedPlace`].
#[derive(Clone, Copy, Deref, DerefMut, PartialEq, Eq, Debug, Hash)]
pub(crate) struct CorrectedPlaceElem<'tcx>(mir::PlaceElem<'tcx>);

/// A place that has been "corrected" from an original mir Place where
/// the type of field projections may be different than what would be expected
/// from the parent struct. See [`Place::with_inherent_region`] for more details.
///
/// The purpose of this wrapper is simply to indicate that this correction has
/// already been performed.
#[derive(Clone, Copy, Deref, DerefMut)]
pub(crate) struct CorrectedPlace<'tcx>(Place<'tcx>);
