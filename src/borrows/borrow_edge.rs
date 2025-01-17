use serde_json::json;

use super::{
    borrow_pcg_edge::{BlockedNode, LocalNode},
    domain::{MaybeOldPlace, MaybeRemotePlace, ToJsonWithRepacker},
    edge_data::EdgeData,
    has_pcs_elem::HasPcsElems,
    region_projection::RegionProjection,
};
use crate::rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHashSet,
    middle::{
        mir::Location,
        ty::{self},
    },
};
use crate::utils::PlaceRepacker;

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BorrowEdge<'tcx> {
    pub blocked_place: MaybeRemotePlace<'tcx>,
    pub assigned_place: MaybeOldPlace<'tcx>,
    mutability: Mutability,

    /// The location when the reborrow was created
    reserve_location: Location,

    pub region: ty::Region<'tcx>,
}

impl<'tcx, T> HasPcsElems<RegionProjection<'tcx, T>> for BorrowEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, T>> {
        vec![]
    }
}

impl<'tcx> EdgeData<'tcx> for BorrowEdge<'tcx> {
    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BlockedNode<'tcx>> {
        vec![self.blocked_place.into()].into_iter().collect()
    }

    fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<super::borrow_pcg_edge::LocalNode<'tcx>> {
        // TODO: Region could be erased and we can't handle that yet
        if let Some(rp) = self.assigned_region_projection(repacker) {
            return vec![LocalNode::RegionProjection(rp.into())].into_iter().collect();
        } else {
            FxHashSet::default()
        }
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }
}

impl<'tcx> BorrowEdge<'tcx> {
    pub (crate) fn new(
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

    pub(crate) fn reserve_location(&self) -> Location {
        self.reserve_location
    }

    pub fn is_mut(&self) -> bool {
        self.mutability == Mutability::Mut
    }

    pub(crate) fn assigned_ref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        self.assigned_place
            .prefix_place(repacker)
            .unwrap()
            .with_inherent_region(repacker)
    }

    pub(crate) fn assigned_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        let assigned_place_ref = self.assigned_ref(repacker);
        if let ty::TyKind::Ref(region, _, _) = assigned_place_ref.ty(repacker).ty.kind() {
            Some(RegionProjection::new(
                (*region).into(),
                assigned_place_ref.into(),
            ))
        } else {
            None
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
