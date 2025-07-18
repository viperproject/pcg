use derive_more::From;

use super::region_projection::{RegionProjection, RegionProjectionLabel};
use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::region_projection::{MaybeRemoteRegionProjectionBase, RegionIdx};
use crate::pcg::{MaybeHasLocation, PCGNodeLike};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::{CompilerCtxt, FilterMutResult, HasPlace, Place, SnapshotLocation};

pub(crate) trait HasPcgElems<T> {
    fn pcg_elems(&mut self) -> Vec<&mut T>;
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub(crate) enum LabelRegionProjectionPredicate<'tcx> {
    Postfix(RegionProjection<'tcx, MaybeOldPlace<'tcx>>),
    Equals(RegionProjection<'tcx, MaybeOldPlace<'tcx>>),
    AllNonPlaceHolder(MaybeOldPlace<'tcx>, RegionIdx),
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for LabelRegionProjectionPredicate<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            LabelRegionProjectionPredicate::Postfix(region_projection) => {
                format!("postfixes of {}", region_projection.to_short_string(ctxt))
            }
            LabelRegionProjectionPredicate::Equals(region_projection) => {
                region_projection.to_short_string(ctxt)
            }
            LabelRegionProjectionPredicate::AllNonPlaceHolder(maybe_old_place, region_idx) => {
                format!(
                    "AllNonPlaceHolder: {}, {:?}",
                    maybe_old_place.to_short_string(ctxt),
                    region_idx
                )
            }
        }
    }
}

impl<'tcx> LabelRegionProjectionPredicate<'tcx> {
    pub(crate) fn matches(
        &self,
        to_match: RegionProjection<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            LabelRegionProjectionPredicate::Equals(projection) => {
                (*projection).rebase() == to_match
            }
            LabelRegionProjectionPredicate::AllNonPlaceHolder(maybe_old_place, region_idx) => {
                to_match.region_idx == *region_idx
                    && to_match.place() == (*maybe_old_place).into()
                    && !to_match.is_placeholder()
            }
            LabelRegionProjectionPredicate::Postfix(predicate_projection) => {
                if let Some(crate::pcg::PCGNode::RegionProjection(to_match)) =
                    to_match.try_to_local_node(ctxt)
                {
                    predicate_projection
                        .base
                        .place()
                        .is_prefix_of(to_match.base.place())
                        && to_match.base.location() == predicate_projection.base.location()
                        && to_match.region_idx == predicate_projection.region_idx
                        && to_match.label() == predicate_projection.label()
                } else {
                    false
                }
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

#[derive(From)]
pub(crate) struct SetLabel(pub(crate) SnapshotLocation);

impl<'tcx> PlaceLabeller<'tcx> for SetLabel {
    fn label_place(&self, _place: Place<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx>) -> SnapshotLocation {
        self.0
    }
}
