use rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHashSet,
    middle::mir::{BasicBlock},
};

use crate::{
    rustc_interface,
    utils::{Place, PlaceRepacker},
};

use super::{
    borrows_graph::Conditioned,
    borrows_state::{RegionProjectionMember, RegionProjectionMemberDirection},
    deref_expansion::DerefExpansion,
    domain::{
        MaybeOldPlace, MaybeRemotePlace, Reborrow,
    },
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection::{HasRegionProjections, RegionProjection},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowsEdge<'tcx> {
    conditions: PathConditions,
    pub(crate) kind: BorrowsEdgeKind<'tcx>,
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

    pub fn blocked_places(&self) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.kind.blocked_places()
    }

    pub fn blocks_place(&self, place: MaybeOldPlace<'tcx>) -> bool {
        self.kind.blocked_places().contains(&place.into())
    }

    pub fn is_blocked_by_place(
        &self,
        place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.kind.blocked_by_places(repacker).contains(&place)
    }

    /// The places that are blocking this edge (e.g. the assigned place of a reborrow)
    pub fn blocked_by_places(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.kind.blocked_by_places(repacker)
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        self.kind.make_place_old(place, latest);
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowsEdgeKind<'tcx> {
    Reborrow(Reborrow<'tcx>),
    DerefExpansion(DerefExpansion<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
    RegionProjectionMember(RegionProjectionMember<'tcx>),
}

impl<'tcx> HasRegionProjections<'tcx> for BorrowsEdgeKind<'tcx> {
    fn region_projections(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        match self {
            BorrowsEdgeKind::RegionProjectionMember(member) => member.region_projections(),
            _ => vec![],
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

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        match self {
            BorrowsEdgeKind::Reborrow(reborrow) => reborrow.make_place_old(place, latest),
            BorrowsEdgeKind::DerefExpansion(de) => de.make_place_old(place, latest),
            BorrowsEdgeKind::Abstraction(abstraction) => abstraction.make_place_old(place, latest),
            BorrowsEdgeKind::RegionProjectionMember(member) => member.make_place_old(place, latest),
        }
    }

    pub fn blocks_place(&self, place: MaybeRemotePlace<'tcx>) -> bool {
        self.blocked_places().contains(&place)
    }

    pub fn blocked_by_place(
        &self,
        place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.blocked_by_places(repacker).contains(&place)
    }

    pub fn blocked_places(&self) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        match &self {
            BorrowsEdgeKind::Reborrow(reborrow) => {
                vec![reborrow.blocked_place].into_iter().collect()
            }
            BorrowsEdgeKind::DerefExpansion(de) => vec![de.base().into()].into_iter().collect(),
            BorrowsEdgeKind::Abstraction(ra) => {
                ra.blocks_places().into_iter().map(|p| p.into()).collect()
            }
            BorrowsEdgeKind::RegionProjectionMember(member) => match member.direction {
                RegionProjectionMemberDirection::PlaceIsRegionInput => {
                    vec![member.place.into()].into_iter().collect()
                }
                RegionProjectionMemberDirection::PlaceIsRegionOutput => FxHashSet::default(),
            },
        }
    }

    /// The places that are blocking this edge (e.g. the assigned place of a reborrow)
    pub fn blocked_by_places(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<MaybeOldPlace<'tcx>> {
        match &self {
            BorrowsEdgeKind::Reborrow(reborrow) => {
                vec![reborrow.assigned_place].into_iter().collect()
            }
            BorrowsEdgeKind::DerefExpansion(de) => de.expansion(repacker).into_iter().collect(),
            BorrowsEdgeKind::Abstraction(ra) => ra.blocked_by_places(),
            BorrowsEdgeKind::RegionProjectionMember(member) => match member.direction {
                RegionProjectionMemberDirection::PlaceIsRegionInput => {
                    vec![member.projection.place].into_iter().collect()
                }
                RegionProjectionMemberDirection::PlaceIsRegionOutput => {
                    vec![member.place.as_local().unwrap()].into_iter().collect()
                }
            },
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

impl<'tcx, T: ToBorrowsEdge<'tcx>> Conditioned<T> {
    pub fn to_borrows_edge(self) -> BorrowsEdge<'tcx> {
        self.value.to_borrows_edge(self.conditions)
    }
}
