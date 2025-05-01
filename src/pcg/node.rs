use crate::borrow_pcg::domain::AbstractionInputTarget;
use crate::borrow_pcg::has_pcs_elem::{
    default_make_place_old, LabelRegionProjection, MakePlaceOld,
};
use crate::borrow_pcg::latest::Latest;
use crate::borrow_pcg::region_projection::RegionProjectionLabel;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::remote::RemotePlace;
use crate::utils::{Place, SnapshotLocation};
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        region_projection::{
            MaybeRemoteRegionProjectionBase, RegionProjection, RegionProjectionBaseLike,
        },
    },
    utils::{display::DisplayWithCompilerCtxt, validity::HasValidityCheck, CompilerCtxt},
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PCGNode<'tcx, T = MaybeRemotePlace<'tcx>, U = MaybeRemoteRegionProjectionBase<'tcx>> {
    Place(T),
    RegionProjection(RegionProjection<'tcx, U>),
}

impl<'tcx> From<AbstractionInputTarget<'tcx>> for PCGNode<'tcx> {
    fn from(target: AbstractionInputTarget<'tcx>) -> Self {
        match target {
            AbstractionInputTarget::Place(p) => PCGNode::Place(p.into()),
            AbstractionInputTarget::RegionProjection(rp) => PCGNode::RegionProjection(rp.into()),
        }
    }
}

impl<'tcx, T, U: Eq + From<MaybeOldPlace<'tcx>>> LabelRegionProjection<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if let PCGNode::RegionProjection(this_projection) = self {
            this_projection.label_region_projection(projection, label, repacker)
        } else {
            false
        }
    }
}

impl<'tcx> MakePlaceOld<'tcx> for PCGNode<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<T, U> From<T> for PCGNode<'_, T, U> {
    fn from(value: T) -> Self {
        PCGNode::Place(value)
    }
}

impl<'tcx, U> From<RegionProjection<'tcx, U>> for PCGNode<'tcx, MaybeRemotePlace<'tcx>, U> {
    fn from(value: RegionProjection<'tcx, U>) -> Self {
        PCGNode::RegionProjection(value)
    }
}

impl<'tcx> From<RegionProjection<'tcx, Place<'tcx>>> for PCGNode<'tcx> {
    fn from(value: RegionProjection<'tcx, Place<'tcx>>) -> Self {
        PCGNode::RegionProjection(value.into())
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for PCGNode<'tcx> {
    fn from(value: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        PCGNode::RegionProjection(value.into())
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> PCGNodeLike<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        match self {
            PCGNode::Place(p) => p.to_pcg_node(repacker),
            PCGNode::RegionProjection(rp) => rp.to_pcg_node(repacker),
        }
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> HasValidityCheck<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        match self {
            PCGNode::Place(p) => p.check_validity(repacker),
            PCGNode::RegionProjection(rp) => rp.check_validity(repacker),
        }
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> DisplayWithCompilerCtxt<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        match self {
            PCGNode::Place(p) => p.to_short_string(repacker),
            PCGNode::RegionProjection(rp) => rp.to_short_string(repacker),
        }
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> ToJsonWithCompilerCtxt<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn to_json(&self, _repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        todo!()
    }
}

pub trait MaybeHasLocation {
    fn location(&self) -> Option<SnapshotLocation>;
}

impl<'tcx, T: MaybeHasLocation, U: RegionProjectionBaseLike<'tcx> + MaybeHasLocation>
    MaybeHasLocation for PCGNode<'tcx, T, U>
{
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            PCGNode::Place(place) => place.location(),
            PCGNode::RegionProjection(region_projection) => region_projection.base().location(),
        }
    }
}

pub trait PCGNodeLike<'tcx>:
    Clone
    + Copy
    + std::fmt::Debug
    + Eq
    + PartialEq
    + std::hash::Hash
    + HasValidityCheck<'tcx>
    + DisplayWithCompilerCtxt<'tcx>
    + ToJsonWithCompilerCtxt<'tcx>
{
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx>;

    fn try_to_local_node<C: Copy>(
        self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<LocalNode<'tcx>> {
        match self.to_pcg_node(repacker) {
            PCGNode::Place(p) => match p {
                MaybeRemotePlace::Local(maybe_old_place) => {
                    Some(maybe_old_place.to_local_node(repacker))
                }
                MaybeRemotePlace::Remote(_) => None,
            },
            PCGNode::RegionProjection(rp) => match rp.base() {
                MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                    match maybe_remote_place {
                        MaybeRemotePlace::Local(maybe_old_place) => Some(
                            rp.with_base(maybe_old_place, repacker)
                                .to_local_node(repacker),
                        ),
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

impl From<RemotePlace> for PCGNode<'_> {
    fn from(remote_place: RemotePlace) -> Self {
        PCGNode::Place(remote_place.into())
    }
}
