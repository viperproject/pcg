use crate::{
    combined_pcs::PCGNode,
    rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHashSet,
        middle::{
            mir::Location,
            ty::{self},
        },
    },
};

use crate::borrow_pcg::borrow_pcg_edge::{BlockedNode, LocalNode};
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::has_pcs_elem::HasPcsElems;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::utils::display::DisplayWithRepacker;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::PlaceRepacker;
use serde_json::json;

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BorrowEdge<'tcx> {
    /// The place that is blocked by the borrow, e.g. the y in `let x = &mut y;`
    pub blocked_place: MaybeRemotePlace<'tcx>,
    /// The place that is assigned by the borrow, e.g. the x in `let x = &mut y;`
    pub(crate) assigned_ref: MaybeOldPlace<'tcx>,
    mutability: Mutability,

    /// The location when the reborrow was created
    reserve_location: Location,

    pub region: ty::Region<'tcx>,
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowEdge<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.blocked_place.check_validity(repacker)?;
        self.assigned_ref.check_validity(repacker)?;
        Ok(())
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for BorrowEdge<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "borrow: {} = &{} {}",
            self.assigned_ref.to_short_string(repacker),
            if self.mutability == Mutability::Mut {
                "mut "
            } else {
                ""
            },
            self.blocked_place.to_short_string(repacker)
        )
    }
}

impl<'tcx, T> HasPcsElems<RegionProjection<'tcx, T>> for BorrowEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, T>> {
        vec![]
    }
}

impl<'tcx> EdgeData<'tcx> for BorrowEdge<'tcx> {
    fn blocks_node(&self, node: BlockedNode<'tcx>, _repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match node {
            PCGNode::Place(p) => self.blocked_place == p,
            PCGNode::RegionProjection(_) => false,
        }
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match node {
            PCGNode::Place(_) => false,
            PCGNode::RegionProjection(region_projection) => {
                region_projection == self.assigned_region_projection(repacker)
            }
        }
    }

    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BlockedNode<'tcx>> {
        vec![self.blocked_place.into()].into_iter().collect()
    }

    fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        let rp = self.assigned_region_projection(repacker);
        return vec![LocalNode::RegionProjection(rp.into())]
            .into_iter()
            .collect();
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }
}

impl<'tcx> BorrowEdge<'tcx> {
    pub(crate) fn new(
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
        mutability: Mutability,
        reservation_location: Location,
        region: ty::Region<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        assert!(assigned_place.ty(repacker).ty.ref_mutability().is_some());
        Self {
            blocked_place,
            assigned_ref: assigned_place,
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

    /// The deref of the assigned place of the borrow. For example, if the borrow is
    /// `let x = &mut y;`, then the deref place is `*x`.
    pub fn deref_place(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        self.assigned_ref.project_deref(repacker)
    }

    /// The region projection associated with the *type* of the assigned place
    /// of the borrow. For example in `let x: &'x mut i32 = ???`, the assigned
    /// region projection is `x↓'x`.
    pub(crate) fn assigned_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
        match self.assigned_ref.ty(repacker).ty.kind() {
            ty::TyKind::Ref(region, _, _) => {
                RegionProjection::new((*region).into(), self.assigned_ref.into(), repacker).unwrap()
            }
            other => unreachable!("{:?}", other),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for BorrowEdge<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "blocked_place": self.blocked_place.to_json(repacker),
            "assigned_place": self.assigned_ref.to_json(repacker),
            "is_mut": self.mutability == Mutability::Mut
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
