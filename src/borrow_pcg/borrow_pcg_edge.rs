use rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::mir::{self, BasicBlock, PlaceElem},
};

use super::{
    borrow_pcg_expansion::BorrowPcgExpansion,
    abstraction_graph_constructor::AbstractionGraphNode,
    edge::{borrow::RemoteBorrow, outlives::BorrowFlowEdge},
    edge_data::EdgeData,
    graph::Conditioned,
    has_pcs_elem::{default_make_place_old, HasPcgElems, LabelRegionProjection, MakePlaceOld},
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_projection::{
        LocalRegionProjection, MaybeRemoteRegionProjectionBase, RegionProjection,
        RegionProjectionLabel,
    },
};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::{borrow_pcg::edge::abstraction::AbstractionType, pcg::PcgError};
use crate::{borrow_pcg::edge::borrow::BorrowEdge, utils::HasPlace};
use crate::{
    edgedata_enum,
    pcg::PCGNode,
    rustc_interface,
    utils::{display::DisplayWithCompilerCtxt, validity::HasValidityCheck, CompilerCtxt, Place},
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowPCGEdgeRef<'tcx, 'graph> {
    pub(crate) kind: &'graph BorrowPcgEdgeKind<'tcx>,
    pub(crate) conditions: &'graph PathConditions,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowPCGEdge<'tcx> {
    pub(crate) conditions: PathConditions,
    pub(crate) kind: BorrowPcgEdgeKind<'tcx>,
}

impl<'tcx> LabelRegionProjection<'tcx> for BorrowPCGEdge<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.kind
            .label_region_projection(projection, label, repacker)
    }
}

impl<'tcx> MakePlaceOld<'tcx> for BorrowPCGEdge<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.kind.make_place_old(place, latest, repacker)
    }
}

impl<'tcx> From<RemoteBorrow<'tcx>> for BorrowPCGEdge<'tcx> {
    fn from(borrow: RemoteBorrow<'tcx>) -> Self {
        BorrowPCGEdge::new(
            borrow.into(),
            PathConditions::AtBlock((mir::Location::START).block),
        )
    }
}

pub trait BorrowPCGEdgeLike<'tcx>: EdgeData<'tcx> + Clone {
    fn kind(&self) -> &BorrowPcgEdgeKind<'tcx>;
    fn conditions(&self) -> &PathConditions;
    fn to_owned_edge(self) -> BorrowPCGEdge<'tcx>;

    /// true iff any of the blocked places can be mutated via the blocking places
    fn is_shared_borrow(&self, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.kind().is_shared_borrow(repacker)
    }

    fn blocked_places<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.blocked_nodes(repacker)
            .into_iter()
            .flat_map(|node| node.as_place())
            .collect()
    }
}

impl<'tcx> BorrowPCGEdgeLike<'tcx> for BorrowPCGEdge<'tcx> {
    fn kind(&self) -> &BorrowPcgEdgeKind<'tcx> {
        &self.kind
    }

    fn conditions(&self) -> &PathConditions {
        &self.conditions
    }

    fn to_owned_edge(self) -> BorrowPCGEdge<'tcx> {
        self
    }
}

impl<'tcx, 'graph> BorrowPCGEdgeLike<'tcx> for BorrowPCGEdgeRef<'tcx, 'graph> {
    fn kind(&self) -> &'graph BorrowPcgEdgeKind<'tcx> {
        self.kind
    }

    fn conditions(&self) -> &PathConditions {
        self.conditions
    }

    fn to_owned_edge(self) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions: self.conditions.clone(),
            kind: self.kind.clone(),
        }
    }
}

impl<'tcx, T: BorrowPCGEdgeLike<'tcx>> HasValidityCheck<'tcx> for T {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        self.kind().check_validity(repacker)
    }
}

impl<'tcx, T: BorrowPCGEdgeLike<'tcx>> DisplayWithCompilerCtxt<'tcx> for T {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "{} under conditions {}",
            self.kind().to_short_string(repacker),
            self.conditions()
        )
    }
}

impl LocalNode<'_> {
    pub(crate) fn is_old(&self) -> bool {
        match self {
            PCGNode::Place(p) => p.is_old(),
            PCGNode::RegionProjection(region_projection) => region_projection.place().is_old(),
        }
    }
}

/// Any node in the PCG that is "local" in the sense that it can be named
/// (include nodes that potentially refer to a past program point), i.e. any
/// node other than a [`RemotePlace`]
pub type LocalNode<'tcx> = PCGNode<'tcx, MaybeOldPlace<'tcx>, MaybeOldPlace<'tcx>>;

impl<'tcx> MakePlaceOld<'tcx> for LocalNode<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<'tcx> From<LocalRegionProjection<'tcx>> for LocalNode<'tcx> {
    fn from(rp: LocalRegionProjection<'tcx>) -> Self {
        LocalNode::RegionProjection(rp)
    }
}

impl<'tcx> TryFrom<LocalNode<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();
    fn try_from(node: LocalNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            LocalNode::Place(maybe_old_place) => Ok(maybe_old_place),
            LocalNode::RegionProjection(_) => Err(()),
        }
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for LocalNode<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            LocalNode::Place(p) => vec![p],
            LocalNode::RegionProjection(rp) => vec![rp.place_mut()],
        }
    }
}

impl<'tcx> HasPcgElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for LocalNode<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        match self {
            LocalNode::Place(_) => vec![],
            LocalNode::RegionProjection(rp) => vec![rp],
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

/// A node that could potentially block other nodes in the PCG, i.e. any node
/// other than a [`RemotePlace`] (which are roots by definition)
pub type BlockingNode<'tcx> = LocalNode<'tcx>;

impl<'tcx> HasPlace<'tcx> for LocalNode<'tcx> {
    fn place(&self) -> Place<'tcx> {
        match self {
            LocalNode::Place(p) => p.place(),
            LocalNode::RegionProjection(rp) => rp.place().place(),
        }
    }

    fn place_mut(&mut self) -> &mut Place<'tcx> {
        match self {
            LocalNode::Place(p) => p.place_mut(),
            LocalNode::RegionProjection(rp) => rp.place_mut().place_mut(),
        }
    }

    fn iter_projections<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Vec<(Self, PlaceElem<'tcx>)> {
        match self {
            LocalNode::Place(p) => p
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
            LocalNode::RegionProjection(rp) => rp
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (LocalNode::RegionProjection(p), e))
                .collect(),
        }
    }

    fn project_deeper<C: Copy>(
        &self,
        elem: mir::PlaceElem<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Result<Self, PcgError> {
        Ok(match self {
            LocalNode::Place(p) => LocalNode::Place(p.project_deeper(elem, repacker)?),
            LocalNode::RegionProjection(rp) => {
                LocalNode::RegionProjection(rp.project_deeper(elem, repacker)?)
            }
        })
    }
}

impl<'tcx> HasValidityCheck<'tcx> for MaybeRemotePlace<'tcx> {
    fn check_validity<C: Copy>(&self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        Ok(())
    }
}

impl<T: std::fmt::Display> std::fmt::Display for PCGNode<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCGNode::Place(p) => write!(f, "{}", p),
            PCGNode::RegionProjection(rp) => write!(f, "{}", rp),
        }
    }
}

impl<'tcx, T> HasPcgElems<RegionProjection<'tcx, MaybeRemoteRegionProjectionBase<'tcx>>>
    for PCGNode<'tcx, T>
{
    fn pcg_elems(
        &mut self,
    ) -> Vec<&mut RegionProjection<'tcx, MaybeRemoteRegionProjectionBase<'tcx>>> {
        match self {
            PCGNode::Place(_) => vec![],
            PCGNode::RegionProjection(rp) => vec![rp],
        }
    }
}

impl<'tcx, T> HasPcgElems<T> for PCGNode<'tcx>
where
    MaybeRemotePlace<'tcx>: HasPcgElems<T>,
    RegionProjection<'tcx>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut T> {
        match self {
            PCGNode::Place(p) => p.pcg_elems(),
            PCGNode::RegionProjection(rp) => rp.pcg_elems(),
        }
    }
}

impl<'tcx> HasPcgElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for PCGNode<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        vec![]
    }
}

pub type BlockedNode<'tcx> = PCGNode<'tcx>;

impl<'tcx> PCGNode<'tcx> {
    pub(crate) fn as_abstraction_graph_node(
        self,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Option<AbstractionGraphNode<'tcx>> {
        match self {
            // Places are allowed only if they are roots of the borrow graph
            PCGNode::Place(place) => match place {
                MaybeRemotePlace::Local(maybe_old_place) => {
                    if maybe_old_place.is_owned(repacker) {
                        Some(PCGNode::Place(place).into())
                    } else {
                        None
                    }
                }
                MaybeRemotePlace::Remote(remote_place) => {
                    Some(PCGNode::Place(remote_place.into()).into())
                }
            },
            PCGNode::RegionProjection(rp) => {
                let rp: RegionProjection<'tcx, MaybeRemotePlace<'tcx>> = rp.try_into().ok()?;
                Some(PCGNode::RegionProjection(rp).into())
            }
        }
    }
    pub(crate) fn as_blocking_node(
        &self,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Option<BlockingNode<'tcx>> {
        self.as_local_node(repacker)
    }

    pub(crate) fn as_local_node<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<LocalNode<'tcx>> {
        match self {
            PCGNode::Place(MaybeRemotePlace::Local(maybe_old_place)) => {
                Some(LocalNode::Place(*maybe_old_place))
            }
            PCGNode::Place(MaybeRemotePlace::Remote(_)) => None,
            PCGNode::RegionProjection(rp) => {
                let place = rp.place().as_local_place()?;
                Some(LocalNode::RegionProjection(rp.with_base(place, repacker)))
            }
        }
    }
    pub fn as_current_place(&self) -> Option<Place<'tcx>> {
        match self {
            BlockedNode::Place(MaybeRemotePlace::Local(MaybeOldPlace::Current { place })) => {
                Some(*place)
            }
            _ => None,
        }
    }

    pub(crate) fn as_place(&self) -> Option<MaybeRemotePlace<'tcx>> {
        match self {
            BlockedNode::Place(maybe_remote_place) => Some(*maybe_remote_place),
            BlockedNode::RegionProjection(_) => None,
        }
    }

    #[allow(unused)]
    pub(crate) fn as_maybe_old_place(&self) -> Option<MaybeOldPlace<'tcx>> {
        self.as_place()?.try_into().ok()
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
    pub fn insert_path_condition(&mut self, pc: PathCondition) -> bool {
        self.conditions.insert(pc)
    }

    pub fn conditions(&self) -> &PathConditions {
        &self.conditions
    }

    pub fn valid_for_path(&self, path: &[BasicBlock]) -> bool {
        self.conditions.valid_for_path(path)
    }

    pub fn kind(&self) -> &BorrowPcgEdgeKind<'tcx> {
        &self.kind
    }

    pub(crate) fn new(kind: BorrowPcgEdgeKind<'tcx>, conditions: PathConditions) -> Self {
        Self { conditions, kind }
    }
}

impl<'tcx, T: BorrowPCGEdgeLike<'tcx>> EdgeData<'tcx> for T {
    fn blocked_by_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.kind().blocked_by_nodes(repacker)
    }

    fn blocked_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<BlockedNode<'tcx>> {
        self.kind().blocked_nodes(repacker)
    }

    fn blocks_node<C: Copy>(
        &self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        self.kind().blocks_node(node, repacker)
    }

    fn is_blocked_by<C: Copy>(
        &self,
        node: LocalNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        self.kind().is_blocked_by(node, repacker)
    }
}

impl<'tcx, T> HasPcgElems<T> for BorrowPCGEdge<'tcx>
where
    BorrowPcgEdgeKind<'tcx>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut T> {
        self.kind.pcg_elems()
    }
}

edgedata_enum!(
    BorrowPcgEdgeKind<'tcx>,
    Borrow(BorrowEdge<'tcx>),
    BorrowPcgExpansion(BorrowPcgExpansion<'tcx>),
    Abstraction(AbstractionType<'tcx>),
    BorrowFlow(BorrowFlowEdge<'tcx>),
);

pub(crate) trait ToBorrowsEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx>;
}

impl<'tcx> ToBorrowsEdge<'tcx> for BorrowPcgExpansion<'tcx, LocalNode<'tcx>> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPcgEdgeKind::BorrowPcgExpansion(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for AbstractionType<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPcgEdgeKind::Abstraction(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for BorrowEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPcgEdgeKind::Borrow(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for BorrowFlowEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPcgEdgeKind::BorrowFlow(self),
        }
    }
}

impl<'tcx, T: ToBorrowsEdge<'tcx>> From<Conditioned<T>> for BorrowPCGEdge<'tcx> {
    fn from(val: Conditioned<T>) -> Self {
        val.value.to_borrow_pcg_edge(val.conditions)
    }
}
