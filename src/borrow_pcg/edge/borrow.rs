use crate::{
    combined_pcs::PCGNode,
    edgedata_enum,
    free_pcs::RepackingBridgeSemiLattice,
    rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHashSet,
        middle::{
            mir::{self, Location},
            ty::{self},
        },
    },
    utils::{remote::RemotePlace, Place},
};

use crate::borrow_pcg::borrow_pcg_edge::{BlockedNode, LocalNode};
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::has_pcs_elem::HasPcgElems;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::utils::display::DisplayWithRepacker;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::PlaceRepacker;
use serde_json::json;

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct LocalBorrow<'tcx> {
    /// The place that is blocked by the borrow, e.g. the y in `let x = &mut y;`
    pub blocked_place: MaybeOldPlace<'tcx>,
    /// The place that is assigned by the borrow, e.g. the x in `let x = &mut y;`
    pub(crate) assigned_ref: MaybeOldPlace<'tcx>,
    mutability: Mutability,

    /// The location when the reborrow was created
    reserve_location: Location,

    pub region: ty::Region<'tcx>,
}

#[derive(Copy, PartialEq, Eq, Clone, Debug, Hash)]
pub struct RemoteBorrow {
    local: mir::Local,
}

impl RemoteBorrow {
    pub(crate) fn blocked_place(&self) -> RemotePlace {
        RemotePlace::new(self.local)
    }

    pub(crate) fn assigned_ref(&self) -> mir::Local {
        self.local
    }

    pub(crate) fn assigned_region_projection<'tcx>(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx, Place<'tcx>> {
        let local_place: Place<'tcx> = self.local.into();
        local_place.base_region_projection(repacker).unwrap()
    }

    pub(crate) fn is_mut<'tcx>(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        let local_place: Place<'tcx> = self.local.into();
        local_place.is_mut_ref(repacker.body(), repacker.tcx())
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for RemoteBorrow {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "{} -> {}",
            self.blocked_place().to_short_string(repacker),
            self.assigned_region_projection(repacker)
                .to_short_string(repacker)
        )
    }
}

impl<'tcx> HasValidityCheck<'tcx> for RemoteBorrow {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl<'tcx> EdgeData<'tcx> for RemoteBorrow {
    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        vec![self.blocked_place().into()].into_iter().collect()
    }

    fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        vec![self.assigned_region_projection(repacker).into()]
            .into_iter()
            .collect()
    }
}

impl RemoteBorrow {
    pub(crate) fn new(local: mir::Local) -> Self {
        Self { local }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowEdge<'tcx> {
    Local(LocalBorrow<'tcx>),
    Remote(RemoteBorrow),
}

edgedata_enum!(
    BorrowEdge<'tcx>,
    Local(LocalBorrow<'tcx>),
    Remote(RemoteBorrow),
);

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for BorrowEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            BorrowEdge::Local(borrow) => borrow.pcg_elems(),
            BorrowEdge::Remote(borrow) => vec![],
        }
    }
}
impl<'tcx> BorrowEdge<'tcx> {
    pub(crate) fn is_mut(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match self {
            BorrowEdge::Local(borrow) => borrow.is_mut(),
            BorrowEdge::Remote(borrow) => borrow.is_mut(repacker),
        }
    }

    pub(crate) fn reserve_location(&self) -> Option<Location> {
        match self {
            BorrowEdge::Local(borrow) => Some(borrow.reserve_location()),
            BorrowEdge::Remote(_) => None,
        }
    }

    pub(crate) fn borrow_region(&self) -> Option<ty::Region<'tcx>> {
        match self {
            BorrowEdge::Local(borrow) => Some(borrow.region),
            BorrowEdge::Remote(_) => None,
        }
    }

    pub(crate) fn assigned_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
        match self {
            BorrowEdge::Local(borrow) => borrow.assigned_region_projection(repacker),
            BorrowEdge::Remote(borrow) => borrow.assigned_region_projection(repacker).into(),
        }
    }

    pub(crate) fn blocked_place(&self) -> MaybeRemotePlace<'tcx> {
        match self {
            BorrowEdge::Local(borrow) => borrow.blocked_place.into(),
            BorrowEdge::Remote(borrow) => borrow.blocked_place().into(),
        }
    }

    pub(crate) fn assigned_ref(&self) -> MaybeOldPlace<'tcx> {
        match self {
            BorrowEdge::Local(borrow) => borrow.assigned_ref,
            BorrowEdge::Remote(remote) => remote.assigned_ref().into(),
        }
    }
}
impl<'tcx> HasValidityCheck<'tcx> for LocalBorrow<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.blocked_place.check_validity(repacker)?;
        self.assigned_ref.check_validity(repacker)?;
        Ok(())
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for LocalBorrow<'tcx> {
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

impl<'tcx, T> HasPcgElems<RegionProjection<'tcx, T>> for BorrowEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, T>> {
        vec![]
    }
}

impl<'tcx> EdgeData<'tcx> for LocalBorrow<'tcx> {
    fn blocks_node(&self, node: BlockedNode<'tcx>, _repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match node {
            PCGNode::Place(MaybeRemotePlace::Local(p)) => self.blocked_place == p,
            _ => false,
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
        vec![LocalNode::RegionProjection(rp)].into_iter().collect()
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }
}

impl<'tcx> LocalBorrow<'tcx> {
    pub(crate) fn new(
        blocked_place: MaybeOldPlace<'tcx>,
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
                RegionProjection::new((*region).into(), self.assigned_ref, repacker).unwrap()
            }
            other => unreachable!("{:?}", other),
        }
    }
}

// impl<'tcx> ToJsonWithRepacker<'tcx> for BorrowEdge<'tcx> {
//     fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
//         json!({
//             "blocked_place": self.blocked_place.to_json(repacker),
//             "assigned_place": self.assigned_ref.to_json(repacker),
//             "is_mut": self.mutability == Mutability::Mut
//         })
//     }
// }

impl std::fmt::Display for BorrowEdge<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "reborrow blocking {} assigned to {}",
            self.blocked_place(),
            self.assigned_ref()
        )
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for LocalBorrow<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.assigned_ref, &mut self.blocked_place]
    }
}
