use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::mir;
use crate::utils::json::ToJsonWithRepacker;
use crate::borrow_pcg::region_projection::{MaybeRemoteRegionProjectionBase, PCGRegion, RegionIdx, RegionProjectionBaseLike};
use crate::combined_pcs::{PCGNode, PCGNodeLike};
use crate::utils::display::DisplayWithRepacker;
use crate::utils::{Place, PlaceRepacker};
use crate::utils::validity::HasValidityCheck;

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct RemotePlace {
    pub(crate) local: mir::Local,
}

impl<'tcx> ToJsonWithRepacker<'tcx> for RemotePlace {
    fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        todo!()
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for RemotePlace {
    fn to_short_string(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!("Remote({:?})", self.local)
    }
}

impl<'tcx> PCGNodeLike<'tcx> for RemotePlace {
    fn to_pcg_node(self) -> PCGNode<'tcx> {
        self.into()
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for RemotePlace {
    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        let place: Place<'_> = self.local.into();
        place.regions(repacker)
    }

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        MaybeRemoteRegionProjectionBase::Place((*self).into())
    }
}

impl<'tcx> HasValidityCheck<'tcx> for RemotePlace {
    fn check_validity(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl std::fmt::Display for RemotePlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Remote({:?})", self.local)
    }
}
