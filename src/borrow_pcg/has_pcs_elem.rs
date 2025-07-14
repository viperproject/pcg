use derive_more::From;

use super::latest::Latest;
use super::region_projection::{RegionProjection, RegionProjectionLabel};
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::region_projection::{MaybeRemoteRegionProjectionBase, RegionIdx};
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::{CompilerCtxt, FilterMutResult, Place, SnapshotLocation};

pub(crate) trait HasPcgElems<T> {
    fn pcg_elems(&mut self) -> Vec<&mut T>;
}

#[derive(From, PartialEq, Eq, Hash, Debug)]
pub(crate) enum LabelRegionProjectionPredicate<'tcx> {
    Equals(RegionProjection<'tcx, MaybeOldPlace<'tcx>>),
    AllNonPlaceHolder(MaybeOldPlace<'tcx>, RegionIdx),
}

impl<'tcx> LabelRegionProjectionPredicate<'tcx> {
    pub(crate) fn matches(
        &self,
        region_projection: RegionProjection<'tcx, MaybeRemoteRegionProjectionBase<'tcx>>,
    ) -> bool {
        match self {
            LabelRegionProjectionPredicate::Equals(projection) => {
                (*projection).rebase() == region_projection
            }
            LabelRegionProjectionPredicate::AllNonPlaceHolder(maybe_old_place, region_idx) => {
                region_projection.region_idx == *region_idx
                    && region_projection.place() == (*maybe_old_place).into()
                    && !region_projection.is_placeholder()
            }
        }
    }
}

impl std::ops::BitOrAssign for LabelRegionProjectionResult {
    fn bitor_assign(&mut self, rhs: Self) {
        if rhs > *self {
            *self = rhs;
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, PartialOrd, Ord)]
pub(crate) enum LabelRegionProjectionResult {
    Unchanged = 0,
    Changed = 1,
    ShouldCollapse = 2,
}

impl LabelRegionProjectionResult {
    pub(crate) fn to_filter_mut_result(self) -> FilterMutResult {
        match self {
            LabelRegionProjectionResult::Changed => FilterMutResult::Changed,
            LabelRegionProjectionResult::Unchanged => FilterMutResult::Unchanged,
            LabelRegionProjectionResult::ShouldCollapse => FilterMutResult::Remove,
        }
    }
}

pub(crate) trait LabelRegionProjection<'tcx> {
    fn label_region_projection(
        &mut self,
        predicate: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelRegionProjectionResult;
}

pub(crate) trait LabelPlace<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

pub(crate) trait PlaceLabeller<'tcx> {
    fn label_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> SnapshotLocation;
}

pub(crate) struct SetLabel(pub(crate) SnapshotLocation);

impl<'tcx> PlaceLabeller<'tcx> for SetLabel {
    fn label_place(&self, _place: Place<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx>) -> SnapshotLocation {
        self.0
    }
}
