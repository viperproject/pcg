use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::remote::RemotePlace;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        region_projection::{
            MaybeRemoteRegionProjectionBase, RegionProjection, RegionProjectionBaseLike,
        },
    },
    utils::{display::DisplayWithRepacker, validity::HasValidityCheck, PlaceRepacker},
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PCGNode<'tcx, T = MaybeRemotePlace<'tcx>, U = MaybeRemoteRegionProjectionBase<'tcx>> {
    Place(T),
    RegionProjection(RegionProjection<'tcx, U>),
}

impl<'tcx> PCGNode<'tcx> {
    pub(crate) fn is_old(&self) -> bool {
        match self {
            PCGNode::Place(p) => p.is_old(),
            PCGNode::RegionProjection(rp) => rp.base().is_old(),
        }
    }
    pub(crate) fn is_owned(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match self {
            PCGNode::Place(p) => p.is_owned(repacker),
            PCGNode::RegionProjection(_) => false,
        }
    }
}

impl<'tcx, T, U> From<T> for PCGNode<'tcx, T, U> {
    fn from(value: T) -> Self {
        PCGNode::Place(value)
    }
}

impl<'tcx, U> From<RegionProjection<'tcx, U>> for PCGNode<'tcx, MaybeRemotePlace<'tcx>, U> {
    fn from(value: RegionProjection<'tcx, U>) -> Self {
        PCGNode::RegionProjection(value)
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> PCGNodeLike<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn to_pcg_node(self, repacker: PlaceRepacker<'_, 'tcx>) -> PCGNode<'tcx> {
        match self {
            PCGNode::Place(p) => p.to_pcg_node(repacker),
            PCGNode::RegionProjection(rp) => rp.to_pcg_node(repacker),
        }
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> HasValidityCheck<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        match self {
            PCGNode::Place(p) => p.check_validity(repacker),
            PCGNode::RegionProjection(rp) => rp.check_validity(repacker),
        }
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> DisplayWithRepacker<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match self {
            PCGNode::Place(p) => p.to_short_string(repacker),
            PCGNode::RegionProjection(rp) => rp.to_short_string(repacker),
        }
    }
}

impl<'tcx, T: PCGNodeLike<'tcx>, U: RegionProjectionBaseLike<'tcx>> ToJsonWithRepacker<'tcx>
    for PCGNode<'tcx, T, U>
{
    fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        todo!()
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
    + DisplayWithRepacker<'tcx>
    + ToJsonWithRepacker<'tcx>
{
    fn to_pcg_node(self, repacker: PlaceRepacker<'_, 'tcx>) -> PCGNode<'tcx>;

    fn try_to_local_node(self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<LocalNode<'tcx>> {
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
                            rp.set_base(maybe_old_place, repacker)
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
    fn to_local_node(self, repacker: PlaceRepacker<'_, 'tcx>) -> LocalNode<'tcx>;
}

impl<'tcx> From<RemotePlace> for PCGNode<'tcx> {
    fn from(remote_place: RemotePlace) -> Self {
        PCGNode::Place(remote_place.into())
    }
}
