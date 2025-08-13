use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::domain::LoopAbstractionInput;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::graph::loop_abstraction::MaybeRemoteCurrentPlace;
use crate::borrow_pcg::has_pcs_elem::{
    LabelLifetimeProjection, LabelLifetimeProjectionPredicate, LabelLifetimeProjectionResult,
    LabelNodeContext, LabelPlaceWithContext, PlaceLabeller,
};
use crate::borrow_pcg::region_projection::LifetimeProjectionLabel;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::maybe_old::MaybeLabelledPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::remote::RemotePlace;
use crate::utils::{HasCompilerCtxt, Place, SnapshotLocation};
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        region_projection::{
            LifetimeProjection, MaybeRemoteRegionProjectionBase, RegionProjectionBaseLike,
        },
    },
    rustc_interface::middle::mir,
    utils::{CompilerCtxt, display::DisplayWithCompilerCtxt, validity::HasValidityCheck},
};

#[deprecated(note = "Use `PcgNode` instead")]
pub type PCGNode<'tcx> = PcgNode<'tcx>;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PcgNode<'tcx, T = MaybeRemotePlace<'tcx>, U = MaybeRemoteRegionProjectionBase<'tcx>> {
    Place(T),
    LifetimeProjection(LifetimeProjection<'tcx, U>),
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for PcgNode<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            PcgNode::Place(p) => {
                p.label_place_with_context(predicate, labeller, label_context, ctxt)
            }
            PcgNode::LifetimeProjection(rp) => {
                rp.label_place_with_context(predicate, labeller, label_context, ctxt)
            }
        }
    }
}

impl<'tcx> PcgNode<'tcx> {
    pub fn related_place(self) -> Option<MaybeRemotePlace<'tcx>> {
        match self {
            PcgNode::Place(p) => Some(p),
            PcgNode::LifetimeProjection(rp) => match rp.base() {
                MaybeRemoteRegionProjectionBase::Place(p) => Some(p),
                _ => None,
            },
        }
    }

    pub fn related_maybe_labelled_place(self) -> Option<MaybeLabelledPlace<'tcx>> {
        self.related_place().and_then(|p| p.as_local_place())
    }

    pub(crate) fn related_maybe_remote_current_place(
        &self,
    ) -> Option<MaybeRemoteCurrentPlace<'tcx>> {
        match self {
            PcgNode::Place(p) => p.maybe_remote_current_place(),
            PcgNode::LifetimeProjection(rp) => rp.base().maybe_remote_current_place(),
        }
    }
}

impl<'tcx, T, U> PcgNode<'tcx, T, U> {
    pub(crate) fn is_place(&self) -> bool {
        matches!(self, PcgNode::Place(_))
    }

    pub(crate) fn try_into_region_projection(self) -> Result<LifetimeProjection<'tcx, U>, Self> {
        match self {
            PcgNode::LifetimeProjection(rp) => Ok(rp),
            _ => Err(self),
        }
    }
}

impl<'tcx> From<LoopAbstractionInput<'tcx>> for PcgNode<'tcx> {
    fn from(target: LoopAbstractionInput<'tcx>) -> Self {
        target.0
    }
}

impl<'tcx, T, U: Copy> LabelLifetimeProjection<'tcx> for PcgNode<'tcx, T, U>
where
    MaybeRemoteRegionProjectionBase<'tcx>: From<U>,
{
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        if let PcgNode::LifetimeProjection(this_projection) = self {
            this_projection.label_lifetime_projection(predicate, label, repacker)
        } else {
            LabelLifetimeProjectionResult::Unchanged
        }
    }
}

impl<T, U> From<T> for PcgNode<'_, T, U> {
    fn from(value: T) -> Self {
        PcgNode::Place(value)
    }
}

impl<'tcx, U> From<LifetimeProjection<'tcx, U>> for PcgNode<'tcx, MaybeRemotePlace<'tcx>, U> {
    fn from(value: LifetimeProjection<'tcx, U>) -> Self {
        PcgNode::LifetimeProjection(value)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>> for PcgNode<'tcx> {
    fn from(value: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        PcgNode::LifetimeProjection(value.into())
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>> for PcgNode<'tcx> {
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        PcgNode::LifetimeProjection(value.into())
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> PCGNodeLike<'tcx>
    for PcgNode<'tcx, T, U>
{
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        match self {
            PcgNode::Place(p) => p.to_pcg_node(repacker),
            PcgNode::LifetimeProjection(rp) => rp.to_pcg_node(repacker),
        }
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> HasValidityCheck<'tcx>
    for PcgNode<'tcx, T, U>
{
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        match self {
            PcgNode::Place(p) => p.check_validity(ctxt),
            PcgNode::LifetimeProjection(rp) => rp.check_validity(ctxt),
        }
    }
}

impl<
    'tcx,
    'a,
    T: PCGNodeLike<'tcx> + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    U: RegionProjectionBaseLike<'tcx>
        + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>> for PcgNode<'tcx, T, U>
{
    fn to_short_string(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            PcgNode::Place(p) => p.to_short_string(repacker),
            PcgNode::LifetimeProjection(rp) => rp.to_short_string(repacker),
        }
    }
}

impl<
    'tcx,
    BC: Copy,
    T: PCGNodeLike<'tcx> + ToJsonWithCompilerCtxt<'tcx, BC>,
    U: RegionProjectionBaseLike<'tcx> + ToJsonWithCompilerCtxt<'tcx, BC>,
> ToJsonWithCompilerCtxt<'tcx, BC> for PcgNode<'tcx, T, U>
{
    fn to_json(&self, _repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        todo!()
    }
}

pub trait MaybeHasLocation {
    fn location(&self) -> Option<SnapshotLocation>;
}

impl<'tcx, T: MaybeHasLocation, U: RegionProjectionBaseLike<'tcx> + MaybeHasLocation>
    MaybeHasLocation for PcgNode<'tcx, T, U>
{
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            PcgNode::Place(place) => place.location(),
            PcgNode::LifetimeProjection(region_projection) => region_projection.base().location(),
        }
    }
}

pub trait PCGNodeLike<'tcx>:
    Clone + Copy + std::fmt::Debug + Eq + PartialEq + std::hash::Hash + HasValidityCheck<'tcx>
{
    fn to_pcg_node<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx>;

    fn try_to_local_node<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Option<LocalNode<'tcx>>
    where
        'tcx: 'a,
    {
        match self.to_pcg_node(ctxt.ctxt()) {
            PcgNode::Place(p) => match p {
                MaybeRemotePlace::Local(maybe_old_place) => {
                    Some(maybe_old_place.to_local_node(ctxt.ctxt()))
                }
                MaybeRemotePlace::Remote(_) => None,
            },
            PcgNode::LifetimeProjection(rp) => match rp.base() {
                MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                    match maybe_remote_place {
                        MaybeRemotePlace::Local(maybe_old_place) => {
                            Some(rp.with_base(maybe_old_place).to_local_node(ctxt.ctxt()))
                        }
                        MaybeRemotePlace::Remote(_) => None,
                    }
                }
                MaybeRemoteRegionProjectionBase::Const(_) => None,
            },
        }
    }
}

pub(crate) trait LocalNodeLike<'tcx> {
    fn to_local_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx>;
}

impl<'tcx> LocalNodeLike<'tcx> for mir::Place<'tcx> {
    fn to_local_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl From<RemotePlace> for PcgNode<'_> {
    fn from(remote_place: RemotePlace) -> Self {
        PcgNode::Place(remote_place.into())
    }
}
