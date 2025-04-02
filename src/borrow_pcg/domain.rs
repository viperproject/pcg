

pub type AbstractionInputTarget<'tcx> = CGNode<'tcx>;

impl<'tcx> TryFrom<AbstractionInputTarget<'tcx>> for RegionProjection<'tcx> {
    type Error = ();

    fn try_from(value: AbstractionInputTarget<'tcx>) -> Result<Self, Self::Error> {
        match value {
            CGNode::RegionProjection(rp) => Ok(rp.into()),
            _ => Err(()),
        }
    }
}

pub type AbstractionOutputTarget<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;

use super::{coupling_graph_constructor::CGNode, region_projection::RegionProjection};
use crate::utils::place::maybe_old::MaybeOldPlace;
