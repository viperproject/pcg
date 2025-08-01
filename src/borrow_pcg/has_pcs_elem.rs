use derive_more::From;

use super::region_projection::{LifetimeProjection, LifetimeProjectionLabel};
use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::region_projection::RegionIdx;
use crate::pcg::{MaybeHasLocation, PCGNodeLike};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeLabelledPlace;
use crate::utils::{CompilerCtxt, FilterMutResult, HasPlace, Place, SnapshotLocation};

pub(crate) trait HasPcgElems<T> {
    fn pcg_elems(&mut self) -> Vec<&mut T>;
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum LabelLifetimeProjectionPredicate<'tcx> {
    Postfix(LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>),
    Equals(LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>),
    AllNonPlaceHolder(MaybeLabelledPlace<'tcx>, RegionIdx),
    AllPlaceholderPostfixes(Place<'tcx>),
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for LabelLifetimeProjectionPredicate<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            LabelLifetimeProjectionPredicate::Postfix(region_projection) => {
                format!("postfixes of {}", region_projection.to_short_string(ctxt))
            }
            LabelLifetimeProjectionPredicate::Equals(region_projection) => {
                region_projection.to_short_string(ctxt)
            }
            LabelLifetimeProjectionPredicate::AllNonPlaceHolder(maybe_old_place, region_idx) => {
                format!(
                    "AllNonPlaceHolder: {}, {:?}",
                    maybe_old_place.to_short_string(ctxt),
                    region_idx
                )
            }
            LabelLifetimeProjectionPredicate::AllPlaceholderPostfixes(place) => {
                format!("AllPlaceholderPostfixes: {}", place.to_short_string(ctxt))
            }
        }
    }
}

impl<'tcx> LabelLifetimeProjectionPredicate<'tcx> {
    pub(crate) fn matches(
        &self,
        to_match: LifetimeProjection<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            LabelLifetimeProjectionPredicate::Equals(projection) => {
                (*projection).rebase() == to_match
            }
            LabelLifetimeProjectionPredicate::AllNonPlaceHolder(maybe_old_place, region_idx) => {
                to_match.region_idx == *region_idx
                    && to_match.place() == (*maybe_old_place).into()
                    && !to_match.is_placeholder()
            }
            LabelLifetimeProjectionPredicate::Postfix(predicate_projection) => {
                if let Some(crate::pcg::PCGNode::LifetimeProjection(to_match)) =
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
            LabelLifetimeProjectionPredicate::AllPlaceholderPostfixes(place) => {
                if let Some(crate::pcg::PCGNode::LifetimeProjection(to_match)) =
                    to_match.try_to_local_node(ctxt)
                {
                    to_match.is_placeholder()
                        && to_match.base.is_current()
                        && place.is_prefix_of(to_match.base.place())
                } else {
                    false
                }
            }
        }
    }
}

impl std::ops::BitOrAssign for LabelLifetimeProjectionResult {
    fn bitor_assign(&mut self, rhs: Self) {
        if rhs > *self {
            *self = rhs;
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, PartialOrd, Ord)]
pub(crate) enum LabelLifetimeProjectionResult {
    Unchanged = 0,
    Changed = 1,
    ShouldCollapse = 2,
}

impl LabelLifetimeProjectionResult {
    pub(crate) fn to_filter_mut_result(self) -> FilterMutResult {
        match self {
            LabelLifetimeProjectionResult::Changed => FilterMutResult::Changed,
            LabelLifetimeProjectionResult::Unchanged => FilterMutResult::Unchanged,
            LabelLifetimeProjectionResult::ShouldCollapse => FilterMutResult::Remove,
        }
    }
}

pub(crate) trait LabelLifetimeProjection<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult;
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub(crate) enum LabelNodeContext {
    TargetOfExpansion,
    Other,
}

pub(crate) trait LabelPlaceWithContext<'tcx, T> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: T,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

impl<'tcx, T: LabelPlace<'tcx>, U> LabelPlaceWithContext<'tcx, U> for T {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        _label_context: U,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.label_place(predicate, labeller, ctxt)
    }
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
