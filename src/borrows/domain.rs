use rustc_interface::{
    ast::Mutability

    ,
    index::IndexVec,
    middle::mir::{self}
    ,
};

use crate::{
    combined_pcs::{PCGNode, PCGNodeLike},
    rustc_interface,
    utils::{
        display::DisplayWithRepacker, validity::HasValidityCheck, HasPlace, Place
        ,
    },
};

pub type AbstractionInputTarget<'tcx> = CGNode<'tcx>;
pub type AbstractionOutputTarget<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;

use crate::utils::PlaceRepacker;
use crate::borrows::edge::borrow::BorrowEdge;
use crate::utils::place::maybe_old::MaybeOldPlace;
use super::{
    coupling_graph_constructor::CGNode
    ,
    has_pcs_elem::HasPcsElems

    ,
    region_projection::{
        MaybeRemoteRegionProjectionBase, PCGRegion, RegionIdx, RegionProjection,
        RegionProjectionBaseLike,
    },
};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct RemotePlace {
    pub(crate) local: mir::Local,
}

impl<'tcx> From<RemotePlace> for PCGNode<'tcx> {
    fn from(remote_place: RemotePlace) -> Self {
        PCGNode::Place(remote_place.into())
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
    fn to_pcg_node(self) -> PCGNode<'tcx> {
        self.into()
    }
}

impl<'tcx> From<RemotePlace> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn from(remote_place: RemotePlace) -> Self {
        MaybeRemoteRegionProjectionBase::Place(remote_place.into())
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

impl RemotePlace {
    pub(crate) fn new(local: mir::Local) -> Self {
        Self { local }
    }

    pub(crate) fn assigned_local(self) -> mir::Local {
        self.local
    }

    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, '_>) -> Mutability {
        let place: Place<'_> = self.local.into();
        place.ref_mutability(repacker).unwrap_or_else(|| {
            if let Ok(root_place) =
                place.is_mutable(crate::utils::LocalMutationIsAllowed::Yes, repacker)
                && root_place.is_local_mutation_allowed == crate::utils::LocalMutationIsAllowed::Yes
            {
                Mutability::Mut
            } else {
                Mutability::Not
            }
        })
    }
}

impl<'tcx> std::fmt::Display for BorrowEdge<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "reborrow blocking {} assigned to {}",
            self.blocked_place, self.assigned_ref
        )
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for BorrowEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut vec = vec![&mut self.assigned_ref];
        vec.extend(self.blocked_place.pcs_elems());
        vec
    }
}

pub trait ToJsonWithRepacker<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value;
}

impl<'tcx, T: ToJsonWithRepacker<'tcx>> ToJsonWithRepacker<'tcx> for Vec<T> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        self.iter()
            .map(|a| a.to_json(repacker))
            .collect::<Vec<_>>()
            .into()
    }
}
