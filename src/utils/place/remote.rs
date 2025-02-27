use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PCGRegion, RegionIdx, RegionProjectionBaseLike,
};
use crate::borrow_pcg::visitor::extract_regions;
use crate::combined_pcs::{PCGNode, PCGNodeLike};
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::{mir, ty::TyCtxt};
use crate::utils::display::DisplayWithRepacker;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::validity::HasValidityCheck;
use crate::utils::{Place, PlaceRepacker};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct RemotePlace {
    pub(crate) local: mir::Local,
}

impl RemotePlace {
    pub(crate) fn deref_place<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Place<'tcx> {
        let place: Place<'_> = self.local.into();
        place
        .0
            .project_deeper(&[mir::ProjectionElem::Deref], tcx)
            .into()
    }
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
    fn to_pcg_node(self, _repacker: PlaceRepacker<'_, 'tcx>) -> PCGNode<'tcx> {
        self.into()
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for RemotePlace {
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        MaybeRemoteRegionProjectionBase::Place((*self).into())
    }

    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        let place: Place<'_> = self.local.into();
        extract_regions(place.ty(repacker).ty)
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
