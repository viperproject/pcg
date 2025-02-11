use crate::{
    borrows::{
        borrow_pcg_edge::LocalNode,
        domain::{MaybeOldPlace, MaybeRemotePlace},
        region_projection::{
            MaybeRemoteRegionProjectionBase, RegionProjection, RegionProjectionBaseLike,
        },
    },
    utils::{display::DisplayWithRepacker, validity::HasValidityCheck, PlaceRepacker},
    ToJsonWithRepacker,
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
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
    fn to_pcg_node(self) -> PCGNode<'tcx> {
        match self {
            PCGNode::Place(p) => p.to_pcg_node(),
            PCGNode::RegionProjection(rp) => rp.to_pcg_node(),
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

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for PCGNode<'tcx> {
    fn from(rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        PCGNode::RegionProjection(rp.map_base(|base| base.into()))
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
    fn to_pcg_node(self) -> PCGNode<'tcx>;

    fn try_to_local_node(self) -> Option<LocalNode<'tcx>> {
        match self.to_pcg_node() {
            PCGNode::Place(p) => match p {
                MaybeRemotePlace::Local(maybe_old_place) => Some(maybe_old_place.to_local_node()),
                MaybeRemotePlace::Remote(_) => None,
            },
            PCGNode::RegionProjection(rp) => match rp.base() {
                MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                    match maybe_remote_place {
                        MaybeRemotePlace::Local(maybe_old_place) => {
                            Some(rp.map_base(|_| maybe_old_place).to_local_node())
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
    fn to_local_node(self) -> LocalNode<'tcx>;
}
