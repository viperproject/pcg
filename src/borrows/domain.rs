use std::collections::HashSet;

use derive_more::From;
use rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHashSet,
    hir::def_id::DefId,
    index::IndexVec,
    middle::mir::{self, tcx::PlaceTy, BasicBlock, Location, PlaceElem},
    middle::ty::GenericArgsRef,
};

use crate::{
    combined_pcs::{LocalNodeLike, PCGNode, PCGNodeLike},
    rustc_interface,
    utils::{
        display::DisplayWithRepacker, validity::HasValidityCheck, HasPlace, Place, PlaceSnapshot,
        SnapshotLocation,
    },
};

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct LoopAbstraction<'tcx> {
    edge: AbstractionBlockEdge<'tcx>,
    block: BasicBlock,
}

impl<'tcx> HasValidityCheck<'tcx> for LoopAbstraction<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.edge.check_validity(repacker)
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for LoopAbstraction<'tcx> {
    fn to_short_string(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!("Loop({:?})", self.block)
    }
}

impl<'tcx, T> HasPcsElems<T> for LoopAbstraction<'tcx>
where
    AbstractionBlockEdge<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        self.edge.pcs_elems()
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for LoopAbstraction<'tcx> {
    fn to_borrow_pcg_edge(self, path_conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge::new(
            super::borrow_pcg_edge::BorrowPCGEdgeKind::Abstraction(AbstractionType::Loop(self)),
            path_conditions,
        )
    }
}

impl<'tcx> LoopAbstraction<'tcx> {
    pub(crate) fn edges(&self) -> Vec<AbstractionBlockEdge<'tcx>> {
        vec![self.edge.clone()]
    }

    pub(crate) fn new(edge: AbstractionBlockEdge<'tcx>, block: BasicBlock) -> Self {
        Self { edge, block }
    }

    pub(crate) fn location(&self) -> Location {
        Location {
            block: self.block,
            statement_index: 0,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallAbstraction<'tcx> {
    location: Location,
    def_id: DefId,
    substs: GenericArgsRef<'tcx>,
    edges: Vec<AbstractionBlockEdge<'tcx>>,
}

impl<'tcx> HasValidityCheck<'tcx> for FunctionCallAbstraction<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        for edge in self.edges.iter() {
            edge.check_validity(repacker)?;
        }
        Ok(())
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for FunctionCallAbstraction<'tcx> {
    fn to_short_string(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!("FunctionCall({:?}, {:?})", self.def_id, self.substs)
    }
}

impl<'tcx, T> HasPcsElems<T> for FunctionCallAbstraction<'tcx>
where
    AbstractionBlockEdge<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        self.edges
            .iter_mut()
            .flat_map(|edge| edge.pcs_elems())
            .collect()
    }
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub fn def_id(&self) -> DefId {
        self.def_id
    }
    pub fn substs(&self) -> GenericArgsRef<'tcx> {
        self.substs
    }

    pub fn location(&self) -> Location {
        self.location
    }

    pub fn edges(&self) -> &Vec<AbstractionBlockEdge<'tcx>> {
        &self.edges
    }

    pub fn new(
        location: Location,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        edges: Vec<AbstractionBlockEdge<'tcx>>,
    ) -> Self {
        assert!(!edges.is_empty());
        Self {
            location,
            def_id,
            substs,
            edges,
        }
    }
}

impl<'tcx> EdgeData<'tcx> for AbstractionType<'tcx> {
    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.inputs().into_iter().map(|i| i.into()).collect()
    }

    fn blocked_by_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        self.outputs()
            .into_iter()
            .map(|o| o.to_local_node())
            .collect()
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum AbstractionType<'tcx> {
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
}

impl<'tcx> DisplayWithRepacker<'tcx> for AbstractionType<'tcx> {
    fn to_short_string(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match self {
            AbstractionType::FunctionCall(c) => c.to_short_string(_repacker),
            AbstractionType::Loop(c) => c.to_short_string(_repacker),
        }
    }
}

impl<'tcx> HasValidityCheck<'tcx> for AbstractionType<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        match self {
            AbstractionType::FunctionCall(c) => c.check_validity(repacker),
            AbstractionType::Loop(c) => c.check_validity(repacker),
        }
    }
}

impl<'tcx, T> HasPcsElems<T> for AbstractionType<'tcx>
where
    LoopAbstraction<'tcx>: HasPcsElems<T>,
    FunctionCallAbstraction<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        match self {
            AbstractionType::FunctionCall(c) => c.pcs_elems(),
            AbstractionType::Loop(c) => c.pcs_elems(),
        }
    }
}

#[derive(Clone, Debug, Hash)]
pub struct AbstractionBlockEdge<'tcx> {
    inputs: Vec<AbstractionInputTarget<'tcx>>,
    outputs: Vec<AbstractionOutputTarget<'tcx>>,
}

impl<'tcx> HasValidityCheck<'tcx> for AbstractionBlockEdge<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        for input in self.inputs.iter() {
            input.check_validity(repacker)?;
        }
        for output in self.outputs.iter() {
            output.check_validity(repacker)?;
        }
        Ok(())
    }
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>>
    for AbstractionBlockEdge<'tcx>
{
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        self.outputs.iter_mut().collect()
    }
}

impl<'tcx> PartialEq for AbstractionBlockEdge<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.inputs() == other.inputs() && self.outputs() == other.outputs()
    }
}

impl<'tcx> Eq for AbstractionBlockEdge<'tcx> {}

impl<'tcx> AbstractionBlockEdge<'tcx> {
    pub(crate) fn new(
        inputs: HashSet<AbstractionInputTarget<'tcx>>,
        outputs: HashSet<AbstractionOutputTarget<'tcx>>,
    ) -> Self {
        Self {
            inputs: inputs.into_iter().collect(),
            outputs: outputs.into_iter().collect(),
        }
    }

    pub fn outputs(&self) -> HashSet<AbstractionOutputTarget<'tcx>> {
        self.outputs.clone().into_iter().collect()
    }

    pub fn inputs(&self) -> HashSet<AbstractionInputTarget<'tcx>> {
        self.inputs.clone().into_iter().collect()
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for AbstractionBlockEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut result = vec![];
        for input in self.inputs.iter_mut() {
            result.extend(input.pcs_elems());
        }
        for output in self.outputs.iter_mut() {
            result.extend(output.pcs_elems());
        }
        result
    }
}

pub type AbstractionInputTarget<'tcx> = CGNode<'tcx>;
pub type AbstractionOutputTarget<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;

impl<'tcx> AbstractionType<'tcx> {
    pub fn location(&self) -> Location {
        match self {
            AbstractionType::FunctionCall(c) => c.location,
            AbstractionType::Loop(c) => c.location(),
        }
    }

    pub fn inputs(&self) -> Vec<AbstractionInputTarget<'tcx>> {
        self.edges()
            .into_iter()
            .flat_map(|edge| edge.inputs())
            .collect()
    }
    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.edges()
            .into_iter()
            .flat_map(|edge| edge.outputs())
            .collect()
    }

    pub fn edges(&self) -> Vec<AbstractionBlockEdge<'tcx>> {
        match self {
            AbstractionType::FunctionCall(c) => c.edges.clone(),
            AbstractionType::Loop(c) => c.edges().clone(),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, From)]
pub enum MaybeOldPlace<'tcx> {
    Current { place: Place<'tcx> },
    OldPlace(PlaceSnapshot<'tcx>),
}

impl<'tcx> LocalNodeLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_local_node(self) -> LocalNode<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_local_node(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_local_node(),
        }
    }
}
impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeOldPlace<'tcx> {
    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        match self {
            MaybeOldPlace::Current { place } => place.regions(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.place.regions(repacker),
        }
    }

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_maybe_remote_region_projection_base(),
            MaybeOldPlace::OldPlace(snapshot) => {
                snapshot.place.to_maybe_remote_region_projection_base()
            }
        }
    }
}
impl<'tcx> PCGNodeLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_pcg_node(self) -> PCGNode<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_pcg_node(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.place.to_pcg_node(),
        }
    }
}

impl<'tcx> TryFrom<MaybeRemoteRegionProjectionBase<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();

    fn try_from(value: MaybeRemoteRegionProjectionBase<'tcx>) -> Result<Self, Self::Error> {
        match value {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                maybe_remote_place.try_into()
            }
            MaybeRemoteRegionProjectionBase::Const(_) => Err(()),
        }
    }
}

impl<'tcx> HasValidityCheck<'tcx> for MaybeOldPlace<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        match self {
            MaybeOldPlace::Current { place } => place.check_validity(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.check_validity(repacker),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for MaybeOldPlace<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeOldPlace::Current { place } => place.to_json(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_json(repacker),
        }
    }
}

impl<'tcx> TryFrom<PCGNode<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();
    fn try_from(node: PCGNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            PCGNode::Place(p) => Ok(p.try_into()?),
            PCGNode::RegionProjection(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<MaybeRemotePlace<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();
    fn try_from(remote_place: MaybeRemotePlace<'tcx>) -> Result<Self, Self::Error> {
        match remote_place {
            MaybeRemotePlace::Local(p) => Ok(p),
            MaybeRemotePlace::Remote(_) => Err(()),
        }
    }
}

impl<'tcx> From<mir::Local> for MaybeOldPlace<'tcx> {
    fn from(local: mir::Local) -> Self {
        Self::Current {
            place: local.into(),
        }
    }
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self::Current {
            place: place.into(),
        }
    }
}

impl<'tcx> std::fmt::Display for MaybeOldPlace<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeOldPlace::Current { place } => write!(f, "{:?}", place),
            MaybeOldPlace::OldPlace(old_place) => write!(f, "{}", old_place),
        }
    }
}

impl<'tcx> HasPlace<'tcx> for MaybeOldPlace<'tcx> {
    fn place(&self) -> Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => *place,
            MaybeOldPlace::OldPlace(old_place) => old_place.place,
        }
    }
    fn place_mut(&mut self) -> &mut Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place,
            MaybeOldPlace::OldPlace(old_place) => &mut old_place.place,
        }
    }

    fn project_deeper(&self, repacker: PlaceRepacker<'_, 'tcx>, elem: PlaceElem<'tcx>) -> Self {
        let mut cloned = self.clone();
        *cloned.place_mut() = self.place().project_deeper(repacker, elem);
        cloned
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for MaybeOldPlace<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        let p = self.place().to_short_string(repacker);
        format!(
            "{}{}",
            p,
            if let Some(location) = self.location() {
                format!(" at {:?}", location)
            } else {
                "".to_string()
            }
        )
    }
}

impl<'tcx> MaybeOldPlace<'tcx> {
    pub fn is_old(&self) -> bool {
        matches!(self, MaybeOldPlace::OldPlace(_))
    }

    pub fn projection(&self) -> &'tcx [PlaceElem<'tcx>] {
        self.place().projection
    }

    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        let place: Place<'_> = self.place();
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
    pub(crate) fn is_owned(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.place().is_owned(repacker)
    }

    pub(crate) fn local(&self) -> mir::Local {
        self.place().local
    }

    pub(crate) fn ty_region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<PCGRegion> {
        self.place().ty_region(repacker)
    }

    pub fn last_projection(&self) -> Option<(Place<'tcx>, PlaceElem<'tcx>)> {
        match self {
            MaybeOldPlace::Current { place } => place.last_projection(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.place.last_projection(),
        }
    }

    pub(crate) fn with_inherent_region(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> MaybeOldPlace<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.with_inherent_region(repacker).into(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.with_inherent_region(repacker).into(),
        }
    }

    pub(crate) fn region_projection(
        &self,
        idx: usize,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx, Self> {
        let region_projections = self.region_projections(repacker);
        if idx < region_projections.len() {
            region_projections[idx]
        } else {
            panic!(
                "Region projection index {:?} out of bounds for place {:?}, ty: {:?}",
                idx,
                self,
                self.ty(repacker)
            );
        }
    }

    pub(crate) fn region_projections(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<RegionProjection<'tcx, Self>> {
        let place = self.with_inherent_region(repacker);
        extract_regions(place.ty(repacker).ty)
            .iter()
            .map(|region| RegionProjection::new((*region).into(), place.into(), repacker))
            .collect()
    }

    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: Option<T>) -> Self {
        if let Some(at) = at {
            Self::OldPlace(PlaceSnapshot::new(place, at))
        } else {
            Self::Current { place }
        }
    }

    pub fn ty(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceTy<'tcx> {
        self.place().ty(repacker)
    }

    pub(crate) fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        MaybeOldPlace::new(self.place().project_deref(repacker).into(), self.location())
    }

    pub fn is_current(&self) -> bool {
        matches!(self, MaybeOldPlace::Current { .. })
    }

    pub fn location(&self) -> Option<SnapshotLocation> {
        match self {
            MaybeOldPlace::Current { .. } => None,
            MaybeOldPlace::OldPlace(old_place) => Some(old_place.at),
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.place().to_json(repacker),
            "at": self.location().map(|loc| format!("{:?}", loc)),
        })
    }

    pub(crate) fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) -> bool {
        if self.is_current() && place.is_prefix(self.place()) {
            *self = MaybeOldPlace::OldPlace(PlaceSnapshot {
                place: self.place(),
                at: latest.get(self.place()),
            });
            true
        } else {
            false
        }
    }
}

use crate::utils::PlaceRepacker;
use serde_json::json;

use super::{
    borrow_edge::BorrowEdge,
    borrow_pcg_edge::{BorrowPCGEdge, LocalNode, ToBorrowsEdge},
    borrows_visitor::extract_regions,
    coupling_graph_constructor::CGNode,
    edge_data::EdgeData,
    has_pcs_elem::HasPcsElems,
    latest::Latest,
    path_condition::PathConditions,
    region_projection::{
        MaybeRemoteRegionProjectionBase, PCGRegion, RegionIdx, RegionProjection,
        RegionProjectionBaseLike,
    },
};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub enum MaybeRemotePlace<'tcx> {
    /// A place that has a name in the program
    Local(MaybeOldPlace<'tcx>),

    /// A place that cannot be named, e.g. the source of a reference-type input argument
    Remote(RemotePlace),
}

impl<'tcx> PCGNodeLike<'tcx> for MaybeRemotePlace<'tcx> {
    fn to_pcg_node(self) -> PCGNode<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.to_pcg_node(),
            MaybeRemotePlace::Remote(rp) => rp.into(),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeRemotePlace<'tcx> {
    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        self.related_local_place().regions(repacker)
    }

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.to_maybe_remote_region_projection_base(),
            MaybeRemotePlace::Remote(rp) => (*rp).into(),
        }
    }
}
impl<'tcx> DisplayWithRepacker<'tcx> for MaybeRemotePlace<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match self {
            MaybeRemotePlace::Local(p) => p.to_short_string(repacker),
            MaybeRemotePlace::Remote(rp) => format!("{}", rp),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for MaybeRemotePlace<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeRemotePlace::Local(p) => p.to_json(repacker),
            MaybeRemotePlace::Remote(rp) => format!("{}", rp).into(),
        }
    }
}

impl<'tcx> From<RemotePlace> for MaybeRemotePlace<'tcx> {
    fn from(remote_place: RemotePlace) -> Self {
        MaybeRemotePlace::Remote(remote_place)
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct RemotePlace {
    local: mir::Local,
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
        todo!()
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

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for MaybeRemotePlace<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(p) => vec![p],
            MaybeRemotePlace::Remote(_) => vec![],
        }
    }
}

impl<'tcx> HasPcsElems<Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut Place<'tcx>> {
        match self {
            MaybeOldPlace::Current { place } => vec![place],
            MaybeOldPlace::OldPlace(snapshot) => snapshot.pcs_elems(),
        }
    }
}

impl<'tcx> std::fmt::Display for MaybeRemotePlace<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeRemotePlace::Local(p) => write!(f, "{}", p),
            MaybeRemotePlace::Remote(l) => write!(f, "Remote({:?})", l),
        }
    }
}

impl<'tcx> MaybeRemotePlace<'tcx> {
    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        match self {
            MaybeRemotePlace::Local(p) => p.mutability(repacker),
            MaybeRemotePlace::Remote(rp) => rp.mutability(repacker),
        }
    }

    pub fn place_assigned_to_local(local: mir::Local) -> Self {
        MaybeRemotePlace::Remote(RemotePlace { local })
    }

    pub(crate) fn is_old(&self) -> bool {
        matches!(self, MaybeRemotePlace::Local(p) if p.is_old())
    }

    pub(crate) fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match self {
            MaybeRemotePlace::Local(p) => p.to_short_string(repacker),
            MaybeRemotePlace::Remote(rp) => format!("{}", rp),
        }
    }

    pub(crate) fn related_local_place(&self) -> Place<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.place(),
            MaybeRemotePlace::Remote(rp) => rp.local.into(),
        }
    }

    pub(crate) fn regions(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> IndexVec<RegionIdx, PCGRegion> {
        self.related_local_place().regions(repacker)
    }

    pub(crate) fn as_current_place(&self) -> Option<Place<'tcx>> {
        if let MaybeRemotePlace::Local(MaybeOldPlace::Current { place }) = self {
            Some(*place)
        } else {
            None
        }
    }

    pub fn as_local_place(&self) -> Option<MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(p) => Some(*p),
            MaybeRemotePlace::Remote(_) => None,
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeRemotePlace::Local(p) => p.to_json(repacker),
            MaybeRemotePlace::Remote(_) => todo!(),
        }
    }

    pub(crate) fn is_owned(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.as_local_place()
            .map(|p| p.is_owned(repacker))
            .unwrap_or(false)
    }
}

impl<'tcx> From<MaybeOldPlace<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: MaybeOldPlace<'tcx>) -> Self {
        MaybeRemotePlace::Local(place)
    }
}

impl<'tcx> From<Place<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        MaybeRemotePlace::Local(place.into())
    }
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        MaybeRemotePlace::Local(place.into())
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
