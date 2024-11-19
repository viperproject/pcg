use serde_json::json;

use super::{
    borrow_pcg_edge::BlockedNode,
    domain::{MaybeOldPlace, MaybeRemotePlace, ToJsonWithRepacker},
    region_projection::RegionProjection,
};
use crate::utils::PlaceRepacker;
use crate::{
    rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHashSet,
        middle::{
            mir::Location,
            ty::{self, RegionVid},
        },
    },
    utils::Place,
};

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BorrowEdge<'tcx> {
    pub blocked_place: MaybeRemotePlace<'tcx>,
    pub assigned_place: MaybeOldPlace<'tcx>,
    mutability: Mutability,

    /// The location when the reborrow was created
    reserve_location: Location,

    pub region: ty::Region<'tcx>,
}

impl<'tcx> BorrowEdge<'tcx> {
    pub fn new(
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
        mutability: Mutability,
        reservation_location: Location,
        region: ty::Region<'tcx>,
    ) -> Self {
        Self {
            blocked_place,
            assigned_place,
            mutability,
            reserve_location: reservation_location,
            region,
        }
    }

    pub fn blocked_nodes(&self) -> FxHashSet<BlockedNode<'tcx>> {
        vec![self.blocked_place.into()].into_iter().collect()
    }

    pub fn reserve_location(&self) -> Location {
        self.reserve_location
    }

    pub fn is_mut(&self) -> bool {
        self.mutability == Mutability::Mut
    }

    pub fn assigned_ref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        self.assigned_place
            .prefix_place(repacker)
            .unwrap()
            .with_inherent_region(repacker)
    }

    // TODO: Region could be erased and we can't handle that yet
    pub fn assigned_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<RegionProjection<'tcx>> {
        let assigned_place_ref = self.assigned_ref(repacker);
        if let ty::TyKind::Ref(region, _, _) = assigned_place_ref.ty(repacker).ty.kind() {
            if let ty::RegionKind::ReVar(v) = region.kind() {
                Some(RegionProjection::new(v, assigned_place_ref))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn region_vid(&self) -> Option<RegionVid> {
        match self.region.kind() {
            ty::RegionKind::ReVar(v) => Some(v),
            _ => None,
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for BorrowEdge<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "blocked_place": self.blocked_place.to_json(repacker),
            "assigned_place": self.assigned_place.to_json(repacker),
            "is_mut": self.mutability == Mutability::Mut
        })
    }
}
