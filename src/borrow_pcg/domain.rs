use super::region_projection::RegionProjection;
use crate::{
    pcg::PCGNode,
    utils::{maybe_remote::MaybeRemotePlace, place::maybe_old::MaybeOldPlace},
};

pub type AbstractionInputTarget<'tcx> =
    PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>;

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for AbstractionInputTarget<'tcx> {
    fn from(value: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        PCGNode::RegionProjection(value.into())
    }
}

impl<'tcx> TryFrom<AbstractionInputTarget<'tcx>> for RegionProjection<'tcx> {
    type Error = ();

    fn try_from(value: AbstractionInputTarget<'tcx>) -> Result<Self, Self::Error> {
        match value {
            PCGNode::RegionProjection(rp) => Ok(rp.into()),
            _ => Err(()),
        }
    }
}

pub type AbstractionOutputTarget<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;
