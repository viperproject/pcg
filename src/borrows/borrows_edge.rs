use rustc_interface::{ast::Mutability, data_structures::fx::FxHashSet, middle::mir::BasicBlock};

use crate::{
    rustc_interface,
    utils::{Place, PlaceRepacker},
};

use super::{
    borrows_graph::Conditioned,
    deref_expansion::DerefExpansion,
    domain::{MaybeOldPlace, MaybeRemotePlace, Reborrow},
    has_pcs_elem::HasPcsElems,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection::RegionProjection,
    region_projection_member::{RegionProjectionMember, RegionProjectionMemberDirection},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowsEdge<'tcx> {
    conditions: PathConditions,
    pub(crate) kind: BorrowsEdgeKind<'tcx>,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BlockingNode<'tcx> {
    Place(MaybeOldPlace<'tcx>),
    RegionProjection(RegionProjection<'tcx>),
}

impl<'tcx> BlockingNode<'tcx> {
    pub fn is_old(&self) -> bool {
        match self {
            BlockingNode::Place(maybe_old_place) => maybe_old_place.is_old(),
            BlockingNode::RegionProjection(rp) => rp.place.is_old(),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BlockedNode<'tcx> {
    Place(MaybeRemotePlace<'tcx>),
    RegionProjection(RegionProjection<'tcx>),
}

impl<'tcx> BlockedNode<'tcx> {
    pub fn is_old(&self) -> bool {
        match self {
            BlockedNode::Place(remote_place) => remote_place.is_old(),
            BlockedNode::RegionProjection(rp) => rp.place.is_old(),
        }
    }

    pub fn as_place(&self) -> Option<MaybeRemotePlace<'tcx>> {
        match self {
            BlockedNode::Place(maybe_remote_place) => Some(*maybe_remote_place),
            BlockedNode::RegionProjection(region_projection) => None,
        }
    }
}

impl<'tcx> From<Place<'tcx>> for BlockedNode<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        BlockedNode::Place(place.into())
    }
}

impl<'tcx> From<RegionProjection<'tcx>> for BlockedNode<'tcx> {
    fn from(rp: RegionProjection<'tcx>) -> Self {
        BlockedNode::RegionProjection(rp)
    }
}

impl<'tcx> From<MaybeOldPlace<'tcx>> for BlockingNode<'tcx> {
    fn from(maybe_old_place: MaybeOldPlace<'tcx>) -> Self {
        BlockingNode::Place(maybe_old_place)
    }
}

impl<'tcx> From<MaybeRemotePlace<'tcx>> for BlockedNode<'tcx> {
    fn from(remote_place: MaybeRemotePlace<'tcx>) -> Self {
        BlockedNode::Place(remote_place)
    }
}

impl<'tcx> From<MaybeOldPlace<'tcx>> for BlockedNode<'tcx> {
    fn from(maybe_old_place: MaybeOldPlace<'tcx>) -> Self {
        BlockedNode::Place(maybe_old_place.into())
    }
}

impl<'tcx> From<BlockingNode<'tcx>> for BlockedNode<'tcx> {
    fn from(blocking_node: BlockingNode<'tcx>) -> Self {
        match blocking_node {
            BlockingNode::Place(maybe_old_place) => BlockedNode::Place(maybe_old_place.into()),
            BlockingNode::RegionProjection(rp) => BlockedNode::RegionProjection(rp),
        }
    }
}

impl<'tcx> BorrowsEdge<'tcx> {
    /// true iff any of the blocked places can be mutated via the blocking places
    pub fn is_shared_borrow(&self) -> bool {
        self.kind.is_shared_borrow()
    }

    pub fn insert_path_condition(&mut self, pc: PathCondition) -> bool {
        self.conditions.insert(pc)
    }

    pub fn conditions(&self) -> &PathConditions {
        &self.conditions
    }
    pub fn valid_for_path(&self, path: &[BasicBlock]) -> bool {
        self.conditions.valid_for_path(path)
    }

    pub fn kind(&self) -> &BorrowsEdgeKind<'tcx> {
        &self.kind
    }

    pub fn mut_kind(&mut self) -> &mut BorrowsEdgeKind<'tcx> {
        &mut self.kind
    }

    pub fn new(kind: BorrowsEdgeKind<'tcx>, conditions: PathConditions) -> Self {
        Self { conditions, kind }
    }

    pub fn blocked_places(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.blocked_nodes(repacker)
            .into_iter()
            .flat_map(|node| node.as_place())
            .collect()
    }

    pub fn blocks_node(&self, repacker: PlaceRepacker<'_, 'tcx>, node: BlockedNode<'tcx>) -> bool {
        self.blocked_nodes(repacker).contains(&node)
    }

    pub fn blocks_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
        rp: RegionProjection<'tcx>,
    ) -> bool {
        self.kind.blocks_region_projection(repacker, rp)
    }

    pub fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<BlockingNode<'tcx>> {
        self.kind.blocked_by_nodes(repacker)
    }

    pub fn blocked_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BlockedNode<'tcx>> {
        self.kind.blocked_nodes(repacker)
    }
}

impl<'tcx, T> HasPcsElems<T> for BorrowsEdge<'tcx>
where
    BorrowsEdgeKind<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        self.kind.pcs_elems()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowsEdgeKind<'tcx> {
    Reborrow(Reborrow<'tcx>),
    DerefExpansion(DerefExpansion<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
    RegionProjectionMember(RegionProjectionMember<'tcx>),
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx>> for BorrowsEdgeKind<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        match self {
            BorrowsEdgeKind::RegionProjectionMember(member) => member.pcs_elems(),
            _ => vec![],
        }
    }
}

impl<'tcx, T> HasPcsElems<T> for BorrowsEdgeKind<'tcx>
where
    Reborrow<'tcx>: HasPcsElems<T>,
    RegionProjectionMember<'tcx>: HasPcsElems<T>,
    DerefExpansion<'tcx>: HasPcsElems<T>,
    AbstractionEdge<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        match self {
            BorrowsEdgeKind::RegionProjectionMember(member) => member.pcs_elems(),
            BorrowsEdgeKind::Reborrow(reborrow) => reborrow.pcs_elems(),
            BorrowsEdgeKind::DerefExpansion(deref_expansion) => deref_expansion.pcs_elems(),
            BorrowsEdgeKind::Abstraction(abstraction_edge) => abstraction_edge.pcs_elems(),
        }
    }
}

impl<'tcx> BorrowsEdgeKind<'tcx> {
    pub fn is_shared_borrow(&self) -> bool {
        match self {
            BorrowsEdgeKind::Reborrow(reborrow) => reborrow.mutability == Mutability::Not,
            _ => false,
        }
    }

    pub fn blocked_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BlockedNode<'tcx>> {
        match self {
            BorrowsEdgeKind::Reborrow(de) => de.blocked_nodes(),
            BorrowsEdgeKind::DerefExpansion(de) => de.blocked_nodes(repacker),
            BorrowsEdgeKind::Abstraction(node) => node.blocked_nodes(),
            BorrowsEdgeKind::RegionProjectionMember(member) => member.blocked_nodes(),
        }
    }

    pub fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<BlockingNode<'tcx>> {
        match self {
            BorrowsEdgeKind::Reborrow(reborrow) => {
                // TODO: Region could be erased and we can't handle that yet
                if let Some(rp) = reborrow.assigned_region_projection(repacker) {
                    return vec![BlockingNode::RegionProjection(rp)]
                        .into_iter()
                        .collect();
                } else {
                    FxHashSet::default()
                }
            }
            BorrowsEdgeKind::Abstraction(node) => node
                .outputs()
                .into_iter()
                .map(|p| BlockingNode::RegionProjection(p))
                .collect(),
            BorrowsEdgeKind::RegionProjectionMember(member) => {
                if member.direction == RegionProjectionMemberDirection::PlaceIsRegionInput {
                    vec![BlockingNode::RegionProjection(member.projection)]
                        .into_iter()
                        .collect()
                } else {
                    vec![BlockingNode::Place(member.place.as_local_place().unwrap())]
                        .into_iter()
                        .collect()
                }
            }
            BorrowsEdgeKind::DerefExpansion(de) => de.blocked_by_nodes(repacker),
        }
    }

    /// Returns true iff this edge directly blocks the given region projection
    pub fn blocks_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
        rp: RegionProjection<'tcx>,
    ) -> bool {
        match &self {
            BorrowsEdgeKind::Reborrow(reborrow) => {
                reborrow.assigned_region_projection(repacker) == Some(rp)
            }
            BorrowsEdgeKind::DerefExpansion(deref_expansion) => {
                for place in deref_expansion.expansion(repacker) {
                    if place.region_projections(repacker).contains(&rp) {
                        return true;
                    }
                }
                false
            }
            BorrowsEdgeKind::Abstraction(abstraction_edge) => {
                abstraction_edge.inputs().contains(&rp)
            }
            BorrowsEdgeKind::RegionProjectionMember(region_projection_member) => todo!(),
        }
    }
}
pub trait ToBorrowsEdge<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx>;
}

impl<'tcx> ToBorrowsEdge<'tcx> for DerefExpansion<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx> {
        BorrowsEdge {
            conditions,
            kind: BorrowsEdgeKind::DerefExpansion(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for AbstractionEdge<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx> {
        BorrowsEdge {
            conditions,
            kind: BorrowsEdgeKind::Abstraction(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for Reborrow<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx> {
        BorrowsEdge {
            conditions,
            kind: BorrowsEdgeKind::Reborrow(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for RegionProjectionMember<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx> {
        BorrowsEdge {
            conditions,
            kind: BorrowsEdgeKind::RegionProjectionMember(self),
        }
    }
}

impl<'tcx, T: ToBorrowsEdge<'tcx>> Into<BorrowsEdge<'tcx>> for Conditioned<T> {
    fn into(self) -> BorrowsEdge<'tcx> {
        self.value.to_borrows_edge(self.conditions)
    }
}
