use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PcgRegion, RegionIdx, RegionProjectionBaseLike,
};
use crate::borrow_pcg::visitor::extract_regions;
use crate::pcg::{PCGNode, PCGNodeLike};
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::mir;
use crate::utils::display::DisplayWithRepacker;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::validity::HasValidityCheck;
use crate::utils::{Place, CompilerCtxt};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct RemotePlace {
    pub(crate) local: mir::Local,
}

impl<'tcx> ToJsonWithRepacker<'tcx> for RemotePlace {
    fn to_json(&self, _repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        todo!()
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for RemotePlace {
    fn to_short_string(&self, _repacker: CompilerCtxt<'_, 'tcx>) -> String {
        format!("Remote({:?})", self.local)
    }
}

impl<'tcx> PCGNodeLike<'tcx> for RemotePlace {
    fn to_pcg_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        self.into()
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for RemotePlace {
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        MaybeRemoteRegionProjectionBase::Place((*self).into())
    }

    fn regions<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> IndexVec<RegionIdx, PcgRegion> {
        let place: Place<'_> = self.local.into();
        extract_regions(place.ty(repacker).ty, repacker)
    }
}

impl<'tcx> HasValidityCheck<'tcx> for RemotePlace {
    fn check_validity<C: Copy>(&self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        Ok(())
    }
}

impl std::fmt::Display for RemotePlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Remote({:?})", self.local)
    }
}
