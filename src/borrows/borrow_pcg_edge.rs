use rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHashSet,
    middle::mir::{self, BasicBlock},
};

use crate::{
    edgedata_enum, rustc_interface,
    utils::{Place, PlaceRepacker},
};

use super::{
    borrow_edge::BorrowEdge,
    borrows_graph::Conditioned,
    coupling_graph_constructor::CGNode,
    deref_expansion::{DerefExpansion, OwnedExpansion},
    domain::{MaybeOldPlace, MaybeRemotePlace, ToJsonWithRepacker},
    edge_data::EdgeData,
    has_pcs_elem::HasPcsElems,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection::RegionProjection,
    region_projection_member::RegionProjectionMember,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowPCGEdge<'tcx> {
    conditions: PathConditions,
    pub(crate) kind: BorrowPCGEdgeKind<'tcx>,
}

/// Any node in the PCG that is "local" in the sense that it can be named
/// (include nodes that potentially refer to a past program point), i.e. any
/// node other than a [`super::domain::RemotePlace`]
pub type LocalNode<'tcx> = PCGNode<'tcx, MaybeOldPlace<'tcx>>;

impl<'tcx> TryFrom<RegionProjection<'tcx>> for LocalNode<'tcx> {
    type Error = ();
    fn try_from(rp: RegionProjection<'tcx>) -> Result<Self, Self::Error> {
        Ok(LocalNode::RegionProjection(rp.try_into()?))
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for LocalNode<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            LocalNode::Place(p) => vec![p],
            LocalNode::RegionProjection(rp) => vec![&mut rp.place],
        }
    }
}

impl<'tcx> From<Place<'tcx>> for LocalNode<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        LocalNode::Place(place.into())
    }
}

impl<'tcx> From<RegionProjection<'tcx, Place<'tcx>>> for LocalNode<'tcx> {
    fn from(rp: RegionProjection<'tcx, Place<'tcx>>) -> Self {
        LocalNode::RegionProjection(rp.into())
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for LocalNode<'tcx> {
    fn from(rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        LocalNode::RegionProjection(rp)
    }
}

/// A node that could potentially block other nodes in the PCG, i.e. any node
/// other than a [`super::domain::RemotePlace`] (which are roots by definition)
pub type BlockingNode<'tcx> = LocalNode<'tcx>;

impl<'tcx> LocalNode<'tcx> {
    pub fn as_cg_node(&self) -> Option<CGNode<'tcx>> {
        match self {
            LocalNode::Place(_) => None,
            LocalNode::RegionProjection(rp) => {
                Some(CGNode::RegionProjection(rp.map_place(|p| p.into())))
            }
        }
    }
    pub fn is_old(&self) -> bool {
        match self {
            LocalNode::Place(maybe_old_place) => maybe_old_place.is_old(),
            LocalNode::RegionProjection(rp) => rp.place.is_old(),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum PCGNode<'tcx, T = MaybeRemotePlace<'tcx>> {
    Place(T),
    RegionProjection(RegionProjection<'tcx, T>),
}

impl<'tcx, T: std::fmt::Display> std::fmt::Display for PCGNode<'tcx, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCGNode::Place(p) => write!(f, "{}", p),
            PCGNode::RegionProjection(rp) => write!(f, "{}", rp),
        }
    }
}

impl<'tcx, T: ToJsonWithRepacker<'tcx>> ToJsonWithRepacker<'tcx> for PCGNode<'tcx, T> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            PCGNode::Place(p) => p.to_json(repacker),
            PCGNode::RegionProjection(rp) => rp.to_json(repacker),
        }
    }
}

impl<'tcx, T> HasPcsElems<RegionProjection<'tcx, T>> for PCGNode<'tcx, T> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, T>> {
        match self {
            PCGNode::Place(_) => vec![],
            PCGNode::RegionProjection(rp) => vec![rp],
        }
    }
}

impl<'tcx, T> HasPcsElems<T> for PCGNode<'tcx>
where
    MaybeRemotePlace<'tcx>: HasPcsElems<T>,
    RegionProjection<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        match self {
            PCGNode::Place(p) => p.pcs_elems(),
            PCGNode::RegionProjection(rp) => rp.pcs_elems(),
        }
    }
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for PCGNode<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        vec![]
    }
}

impl<'tcx, T: Into<MaybeRemotePlace<'tcx>>> From<RegionProjection<'tcx, T>> for PCGNode<'tcx> {
    fn from(rp: RegionProjection<'tcx, T>) -> Self {
        PCGNode::RegionProjection(rp.map_place(|p| p.into()))
    }
}

impl<'tcx> From<CGNode<'tcx>> for PCGNode<'tcx> {
    fn from(cg_node: CGNode<'tcx>) -> Self {
        match cg_node {
            CGNode::RegionProjection(rp) => PCGNode::RegionProjection(rp),
            CGNode::RemotePlace(rp) => PCGNode::Place(rp.into()),
        }
    }
}

pub type BlockedNode<'tcx> = PCGNode<'tcx>;

impl<'tcx> PCGNode<'tcx> {
    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        match self {
            PCGNode::Place(rp) => rp.mutability(repacker),
            PCGNode::RegionProjection(rp) => rp.mutability(repacker),
        }
    }

    pub(crate) fn as_cg_node(self) -> Option<CGNode<'tcx>> {
        match self {
            PCGNode::Place(MaybeRemotePlace::Remote(remote_place)) => {
                Some(CGNode::RemotePlace(remote_place))
            }
            PCGNode::RegionProjection(rp) => Some(CGNode::RegionProjection(rp)),
            PCGNode::Place(MaybeRemotePlace::Local(_)) => None,
        }
    }
    pub(crate) fn as_blocking_node(&self) -> Option<BlockingNode<'tcx>> {
        self.as_local_node()
    }

    pub(crate) fn as_local_node(&self) -> Option<LocalNode<'tcx>> {
        match self {
            PCGNode::Place(MaybeRemotePlace::Local(maybe_old_place)) => {
                Some(LocalNode::Place(*maybe_old_place))
            }
            PCGNode::Place(MaybeRemotePlace::Remote(_)) => None,
            PCGNode::RegionProjection(rp) => {
                let place = rp.place.as_local_place()?;
                Some(LocalNode::RegionProjection(rp.map_place(|_| place)))
            }
        }
    }
    pub(crate) fn as_current_place(&self) -> Option<Place<'tcx>> {
        match self {
            BlockedNode::Place(MaybeRemotePlace::Local(MaybeOldPlace::Current { place })) => {
                Some(*place)
            }
            _ => None,
        }
    }

    pub(crate) fn is_old(&self) -> bool {
        match self {
            BlockedNode::Place(remote_place) => remote_place.is_old(),
            BlockedNode::RegionProjection(rp) => rp.place.is_old(),
        }
    }

    pub(crate) fn as_place(&self) -> Option<MaybeRemotePlace<'tcx>> {
        match self {
            BlockedNode::Place(maybe_remote_place) => Some(*maybe_remote_place),
            BlockedNode::RegionProjection(_) => None,
        }
    }
}

impl<'tcx> From<mir::Place<'tcx>> for BlockedNode<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        BlockedNode::Place(place.into())
    }
}

impl<'tcx> From<Place<'tcx>> for BlockedNode<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        BlockedNode::Place(place.into())
    }
}

impl<'tcx> From<MaybeOldPlace<'tcx>> for LocalNode<'tcx> {
    fn from(maybe_old_place: MaybeOldPlace<'tcx>) -> Self {
        LocalNode::Place(maybe_old_place)
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

impl<'tcx> From<LocalNode<'tcx>> for BlockedNode<'tcx> {
    fn from(blocking_node: LocalNode<'tcx>) -> Self {
        match blocking_node {
            LocalNode::Place(maybe_old_place) => BlockedNode::Place(maybe_old_place.into()),
            LocalNode::RegionProjection(rp) => BlockedNode::RegionProjection(rp.into()),
        }
    }
}

impl<'tcx> BorrowPCGEdge<'tcx> {
    /// true iff any of the blocked places can be mutated via the blocking places
    pub(crate) fn is_shared_borrow(&self) -> bool {
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

    pub fn kind(&self) -> &BorrowPCGEdgeKind<'tcx> {
        &self.kind
    }

    pub(crate) fn new(kind: BorrowPCGEdgeKind<'tcx>, conditions: PathConditions) -> Self {
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

    pub fn blocks_node(&self, node: BlockedNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.blocked_nodes(repacker).contains(&node)
    }
}

impl<'tcx> EdgeData<'tcx> for BorrowPCGEdge<'tcx> {
    fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        self.kind.blocked_by_nodes(repacker)
    }

    fn blocked_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BlockedNode<'tcx>> {
        self.kind.blocked_nodes(repacker)
    }

    fn is_owned_expansion(&self) -> bool {
        self.kind.is_owned_expansion()
    }
}

impl<'tcx, T> HasPcsElems<T> for BorrowPCGEdge<'tcx>
where
    BorrowPCGEdgeKind<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        self.kind.pcs_elems()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowPCGEdgeKind<'tcx> {
    Borrow(BorrowEdge<'tcx>),
    DerefExpansion(DerefExpansion<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
    RegionProjectionMember(RegionProjectionMember<'tcx>),
}

edgedata_enum!(
    BorrowPCGEdgeKind<'tcx>,
    Borrow(BorrowEdge<'tcx>),
    DerefExpansion(DerefExpansion<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
    RegionProjectionMember(RegionProjectionMember<'tcx>)
);

impl<'tcx> From<OwnedExpansion<'tcx>> for BorrowPCGEdgeKind<'tcx> {
    fn from(owned_expansion: OwnedExpansion<'tcx>) -> Self {
        BorrowPCGEdgeKind::DerefExpansion(DerefExpansion::OwnedExpansion(owned_expansion))
    }
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx>> for BorrowPCGEdgeKind<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        match self {
            BorrowPCGEdgeKind::RegionProjectionMember(member) => member.pcs_elems(),
            _ => vec![],
        }
    }
}

impl<'tcx, T> HasPcsElems<T> for BorrowPCGEdgeKind<'tcx>
where
    BorrowEdge<'tcx>: HasPcsElems<T>,
    RegionProjectionMember<'tcx>: HasPcsElems<T>,
    DerefExpansion<'tcx>: HasPcsElems<T>,
    AbstractionEdge<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        match self {
            BorrowPCGEdgeKind::RegionProjectionMember(member) => member.pcs_elems(),
            BorrowPCGEdgeKind::Borrow(reborrow) => reborrow.pcs_elems(),
            BorrowPCGEdgeKind::DerefExpansion(deref_expansion) => deref_expansion.pcs_elems(),
            BorrowPCGEdgeKind::Abstraction(abstraction_edge) => abstraction_edge.pcs_elems(),
        }
    }
}

impl<'tcx> BorrowPCGEdgeKind<'tcx> {
    pub(crate) fn is_shared_borrow(&self) -> bool {
        match self {
            BorrowPCGEdgeKind::Borrow(reborrow) => !reborrow.is_mut(),
            _ => false,
        }
    }
}
pub (crate) trait ToBorrowsEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx>;
}

impl<'tcx> ToBorrowsEdge<'tcx> for DerefExpansion<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPCGEdgeKind::DerefExpansion(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for AbstractionEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPCGEdgeKind::Abstraction(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for BorrowEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPCGEdgeKind::Borrow(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for RegionProjectionMember<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPCGEdgeKind::RegionProjectionMember(self),
        }
    }
}

impl<'tcx, T: ToBorrowsEdge<'tcx>> Into<BorrowPCGEdge<'tcx>> for Conditioned<T> {
    fn into(self) -> BorrowPCGEdge<'tcx> {
        self.value.to_borrow_pcg_edge(self.conditions)
    }
}
