use std::collections::HashSet;

use rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHashSet,
    hir::def_id::DefId,
    middle::mir::{self, tcx::PlaceTy, BasicBlock, Location, PlaceElem},
    middle::ty::{self, GenericArgsRef, RegionVid, TyCtxt},
};

use crate::{
    rustc_interface,
    utils::{Place, PlaceSnapshot, SnapshotLocation},
};

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct LoopAbstraction<'tcx> {
    edge: AbstractionBlockEdge<'tcx>,
    block: BasicBlock,
}

impl<'tcx> ToBorrowsEdge<'tcx> for LoopAbstraction<'tcx> {
    fn to_borrows_edge(self, path_conditions: PathConditions) -> BorrowsEdge<'tcx> {
        BorrowsEdge::new(
            super::borrows_edge::BorrowsEdgeKind::Abstraction(AbstractionEdge {
                abstraction_type: AbstractionType::Loop(self),
            }),
            path_conditions,
        )
    }
}

impl<'tcx> LoopAbstraction<'tcx> {
    pub fn inputs(&self) -> Vec<AbstractionInputTarget<'tcx>> {
        self.edge.inputs().into_iter().collect()
    }

    pub fn edges(&self) -> Vec<AbstractionBlockEdge<'tcx>> {
        vec![self.edge.clone()]
    }
    pub fn new(edge: AbstractionBlockEdge<'tcx>, block: BasicBlock) -> Self {
        Self { edge, block }
    }

    pub fn location(&self) -> Location {
        Location {
            block: self.block,
            statement_index: 0,
        }
    }

    pub fn maybe_old_places(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.edge.maybe_old_places()
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallAbstraction<'tcx> {
    location: Location,

    def_id: DefId,

    substs: GenericArgsRef<'tcx>,

    edges: Vec<(usize, AbstractionBlockEdge<'tcx>)>,
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub fn maybe_old_places(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.edges
            .iter_mut()
            .flat_map(|(_, edge)| edge.maybe_old_places())
            .collect()
    }

    pub fn def_id(&self) -> DefId {
        self.def_id
    }
    pub fn substs(&self) -> GenericArgsRef<'tcx> {
        self.substs
    }

    pub fn location(&self) -> Location {
        self.location
    }
    pub fn edges(&self) -> &Vec<(usize, AbstractionBlockEdge<'tcx>)> {
        &self.edges
    }
    pub fn new(
        location: Location,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        edges: Vec<(usize, AbstractionBlockEdge<'tcx>)>,
    ) -> Self {
        assert!(edges.len() > 0);
        Self {
            location,
            def_id,
            substs,
            edges,
        }
    }
}

pub trait HasPlaces<'tcx> {
    fn places_mut(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>>;

    fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        for p in self.places_mut() {
            p.make_place_old(place, latest);
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum AbstractionType<'tcx> {
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
}

#[derive(Clone, Debug, Hash)]
pub struct AbstractionBlockEdge<'tcx> {
    inputs: Vec<AbstractionInputTarget<'tcx>>,
    outputs: Vec<AbstractionOutputTarget<'tcx>>,
}

impl<'tcx> PartialEq for AbstractionBlockEdge<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.inputs() == other.inputs() && self.outputs() == other.outputs()
    }
}

impl<'tcx> Eq for AbstractionBlockEdge<'tcx> {}

impl<'tcx> AbstractionBlockEdge<'tcx> {
    pub fn new(
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

    pub fn maybe_old_places(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut result = vec![];
        for input in self.inputs.iter_mut() {
            if let Some(place) = input.mut_place() {
                result.push(place);
            }
        }
        for output in self.outputs.iter_mut() {
            result.push(output.mut_place());
        }
        result
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum AbstractionTarget<'tcx, T> {
    Place(T),
    RegionProjection(RegionProjection<'tcx>),
}

pub type AbstractionInputTarget<'tcx> = AbstractionTarget<'tcx, MaybeRemotePlace<'tcx>>;
pub type AbstractionOutputTarget<'tcx> = AbstractionTarget<'tcx, MaybeOldPlace<'tcx>>;

impl<'tcx> AbstractionInputTarget<'tcx> {
    pub fn blocks(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        match self {
            AbstractionTarget::Place(p) => match p {
                MaybeRemotePlace::Local(maybe_old_place) => maybe_old_place == place,
                MaybeRemotePlace::Remote(_local) => false,
            },
            AbstractionTarget::RegionProjection(_p) => false,
        }
    }

    pub fn mut_place(&mut self) -> Option<&mut MaybeOldPlace<'tcx>> {
        match self {
            AbstractionTarget::Place(bp) => match bp {
                MaybeRemotePlace::Local(ref mut maybe_old_place) => Some(maybe_old_place),
                MaybeRemotePlace::Remote(_) => None,
            },
            AbstractionTarget::RegionProjection(p) => Some(&mut p.place),
        }
    }
}

impl<'tcx> AbstractionOutputTarget<'tcx> {
    pub fn mut_place(&mut self) -> &mut MaybeOldPlace<'tcx> {
        match self {
            AbstractionTarget::Place(p) => p,
            AbstractionTarget::RegionProjection(p) => &mut p.place,
        }
    }
}

impl<'tcx, T: HasPlaces<'tcx>> AbstractionTarget<'tcx, T> {
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        match self {
            AbstractionTarget::Place(p) => p.make_place_old(place, latest),
            AbstractionTarget::RegionProjection(p) => p.make_place_old(place, latest),
        }
    }

    // pub fn region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> RegionVid {
    //     match self {
    //         AbstractionTarget::Place(p) => {
    //             let prefix = p.place().prefix_place(repacker);
    //             match prefix.unwrap().ty(repacker).ty.kind() {
    //                 ty::Ref(region, _, _) => match region.kind() {
    //                     ty::RegionKind::ReVar(v) => v,
    //                     _ => unreachable!(),
    //                 },
    //                 _ => unreachable!(),
    //             }
    //         }
    //         AbstractionTarget::RegionProjection(p) => p.region,
    //     }
    // }
}

impl<'tcx> AbstractionType<'tcx> {
    pub fn maybe_old_places(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            AbstractionType::FunctionCall(c) => c.maybe_old_places(),
            AbstractionType::Loop(c) => c.maybe_old_places(),
        }
    }

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

    pub fn blocks_places(&self) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.edges()
            .into_iter()
            .flat_map(|edge| edge.inputs())
            .flat_map(|input| match input {
                AbstractionTarget::Place(p) => Some(p),
                AbstractionTarget::RegionProjection(_) => None,
            })
            .collect()
    }

    pub fn edges(&self) -> Vec<AbstractionBlockEdge<'tcx>> {
        match self {
            AbstractionType::FunctionCall(c) => {
                c.edges.iter().map(|(_, edge)| edge).cloned().collect()
            }
            AbstractionType::Loop(c) => c.edges().clone(),
        }
    }

    pub fn blocker_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.edges()
            .into_iter()
            .flat_map(|edge| edge.outputs())
            .flat_map(|output| match output {
                AbstractionTarget::Place(p) => Some(p),
                AbstractionTarget::RegionProjection(_) => None,
            })
            .collect()
    }

    pub fn blocks(&self, place: MaybeRemotePlace<'tcx>) -> bool {
        self.blocks_places().contains(&place)
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        for p in self.maybe_old_places() {
            p.make_place_old(place, latest);
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum MaybeOldPlace<'tcx> {
    Current { place: Place<'tcx> },
    OldPlace(PlaceSnapshot<'tcx>),
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self::Current {
            place: place.into(),
        }
    }
}

impl<'tcx> From<PlaceSnapshot<'tcx>> for MaybeOldPlace<'tcx> {
    fn from(snapshot: PlaceSnapshot<'tcx>) -> Self {
        Self::OldPlace(snapshot)
    }
}

impl<'tcx> std::fmt::Display for MaybeOldPlace<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeOldPlace::Current { place } => write!(f, "{:?}", place),
            MaybeOldPlace::OldPlace(old_place) => write!(f, "{:?}", old_place),
        }
    }
}

impl<'tcx> MaybeOldPlace<'tcx> {
    pub fn with_inherent_region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.with_inherent_region(repacker).into(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.with_inherent_region(repacker).into(),
        }
    }

    pub fn prefix_place(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        match self {
            MaybeOldPlace::Current { place } => Some(place.prefix_place(repacker)?.into()),
            MaybeOldPlace::OldPlace(snapshot) => Some(snapshot.prefix_place(repacker)?.into()),
        }
    }

    pub fn region_projection(
        &self,
        idx: usize,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx> {
        RegionProjection::new(self.region_projections(repacker)[idx].region, self.clone())
    }

    pub fn region_projections(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<RegionProjection<'tcx>> {
        extract_lifetimes(self.ty(repacker).ty)
            .iter()
            .map(|region| RegionProjection::new(get_vid(region).unwrap(), self.clone()))
            .collect()
    }

    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: Option<T>) -> Self {
        if let Some(at) = at {
            Self::OldPlace(PlaceSnapshot::new(place, at))
        } else {
            Self::Current { place }
        }
    }

    pub fn as_current(&self) -> Option<Place<'tcx>> {
        match self {
            MaybeOldPlace::Current { place } => Some(*place),
            MaybeOldPlace::OldPlace(_) => None,
        }
    }

    pub fn old_place(&self) -> Option<PlaceSnapshot<'tcx>> {
        match self {
            MaybeOldPlace::Current { .. } => None,
            MaybeOldPlace::OldPlace(old_place) => Some(old_place.clone()),
        }
    }

    pub fn ty(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceTy<'tcx> {
        self.place().ty(repacker)
    }

    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        MaybeOldPlace::new(self.place().project_deref(repacker).into(), self.location())
    }
    pub fn project_deeper(&self, tcx: TyCtxt<'tcx>, elem: PlaceElem<'tcx>) -> MaybeOldPlace<'tcx> {
        MaybeOldPlace::new(
            self.place().project_deeper(&[elem], tcx).into(),
            self.location(),
        )
    }

    pub fn is_mut_ref(&self, body: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        self.place().is_mut_ref(body, tcx)
    }

    pub fn is_ref(&self, body: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        self.place().is_ref(body, tcx)
    }

    pub fn is_current(&self) -> bool {
        matches!(self, MaybeOldPlace::Current { .. })
    }

    pub fn is_old(&self) -> bool {
        matches!(self, MaybeOldPlace::OldPlace(_))
    }

    pub fn place(&self) -> Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => *place,
            MaybeOldPlace::OldPlace(old_place) => old_place.place,
        }
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

    pub fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
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
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        if self.is_current() && place.is_prefix(self.place()) {
            *self = MaybeOldPlace::OldPlace(PlaceSnapshot {
                place: self.place(),
                at: latest.get(&self.place()),
            });
        }
    }
}

use crate::utils::PlaceRepacker;
use serde_json::json;

use super::{
    borrows_edge::{BorrowsEdge, ToBorrowsEdge},
    borrows_visitor::{extract_lifetimes, get_vid},
    latest::Latest,
    path_condition::PathConditions,
    region_abstraction::AbstractionEdge,
    region_projection::RegionProjection,
};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub enum MaybeRemotePlace<'tcx> {
    /// Reborrows from a place that has a name in the program, e.g for a
    /// reborrow x = &mut (*y), the blocked place is `Local(*y)`
    Local(MaybeOldPlace<'tcx>),

    /// The blocked place that a borrows in function inputs; e.g for a function
    /// `f(&mut x)` the blocked place is `Remote(x)`
    Remote(mir::Local),
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
    pub fn is_old(&self) -> bool {
        matches!(self, MaybeRemotePlace::Local(p) if p.is_old())
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        match self {
            MaybeRemotePlace::Local(p) => p.make_place_old(place, latest),
            MaybeRemotePlace::Remote(_) => {}
        }
    }

    pub fn as_local(&self) -> Option<MaybeOldPlace<'tcx>> {
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

impl<'tcx> std::fmt::Display for Reborrow<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "reborrow blocking {} assigned to {}",
            self.blocked_place, self.assigned_place
        )
    }
}
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Reborrow<'tcx> {
    pub blocked_place: MaybeRemotePlace<'tcx>,
    pub assigned_place: MaybeOldPlace<'tcx>,
    pub mutability: Mutability,

    /// The location when the reborrow was created
    reserve_location: Location,

    pub region: ty::Region<'tcx>,
}

impl<'tcx> Reborrow<'tcx> {
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

    pub fn region_projection_edges(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<(RegionProjection<'tcx>, RegionProjection<'tcx>)> {
        if let (Some(blocked_place_prefix), Some(assigned_place_prefix)) = (
            self.blocked_place_prefix(repacker),
            self.assigned_place_prefix(repacker),
        ) {
            RegionProjection::connections_between_places(
                blocked_place_prefix.with_inherent_region(repacker),
                assigned_place_prefix.with_inherent_region(repacker),
                repacker,
            )
        } else {
            FxHashSet::default()
        }
    }

    fn blocked_place_prefix(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<MaybeOldPlace<'tcx>> {
        match self.blocked_place {
            MaybeRemotePlace::Local(maybe_old_place) => {
                Some(maybe_old_place.prefix_place(repacker).unwrap())
            }
            MaybeRemotePlace::Remote(local) => Some(MaybeOldPlace::Current {
                place: local.into(),
            }),
        }
    }

    fn assigned_place_prefix(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<MaybeOldPlace<'tcx>> {
        self.assigned_place.prefix_place(repacker)
    }

    pub fn reserve_location(&self) -> Location {
        self.reserve_location
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        self.blocked_place.make_place_old(place, latest);
        self.assigned_place.make_place_old(place, latest);
    }

    pub fn assiged_place_region_vid(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<RegionVid> {
        match self
            .assigned_place
            .place()
            .prefix_place(repacker)
            .unwrap()
            .ty(repacker)
            .ty
            .kind()
        {
            ty::Ref(region, _, _) => match region.kind() {
                ty::RegionKind::ReVar(v) => Some(v),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn region_vid(&self) -> Option<RegionVid> {
        match self.region.kind() {
            ty::RegionKind::ReVar(v) => Some(v),
            _ => None,
        }
    }
}

pub trait ToJsonWithRepacker<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value;
}

impl<'tcx> ToJsonWithRepacker<'tcx> for Reborrow<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "blocked_place": self.blocked_place.to_json(repacker),
            "assigned_place": self.assigned_place.to_json(repacker),
            "is_mut": self.mutability == Mutability::Mut
        })
    }
}
