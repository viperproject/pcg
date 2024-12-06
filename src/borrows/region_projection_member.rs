use crate::rustc_interface::{ast::Mutability, data_structures::fx::FxHashSet};
use crate::utils::PlaceRepacker;

use super::borrow_pcg_edge::{LocalNode, PCGNode};
use super::edge_data::EdgeData;
use super::{
    borrow_pcg_edge::BlockedNode,
    domain::{MaybeOldPlace, MaybeRemotePlace},
    has_pcs_elem::HasPcsElems,
    region_projection::RegionProjection,
};
#[derive(Clone, Debug, Hash, PartialEq, Eq, Copy)]
pub enum RegionProjectionMemberDirection {
    ProjectionBlocksPlace,
    PlaceBlocksProjection,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RegionProjectionMember<'tcx> {
    pub place: MaybeRemotePlace<'tcx>,
    pub projection: RegionProjection<'tcx>,
    direction: RegionProjectionMemberDirection,
}

impl<'tcx> EdgeData<'tcx> for RegionProjectionMember<'tcx> {
    fn blocked_by_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        let blocked_by_node = match self.direction {
            RegionProjectionMemberDirection::ProjectionBlocksPlace => {
                LocalNode::RegionProjection(self.projection)
            }
            RegionProjectionMemberDirection::PlaceBlocksProjection => {
                LocalNode::Place(self.place.as_local_place().unwrap())
            }
        };
        vec![blocked_by_node].into_iter().collect()
    }

    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        let blocked = match self.direction {
            RegionProjectionMemberDirection::ProjectionBlocksPlace => self.place.into(),
            RegionProjectionMemberDirection::PlaceBlocksProjection => self.projection.into(),
        };
        vec![blocked].into_iter().collect()
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx>> for RegionProjectionMember<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        vec![&mut self.projection]
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjectionMember<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut vec = self.place.pcs_elems();
        vec.extend(self.projection.pcs_elems());
        vec
    }
}

impl<'tcx> RegionProjectionMember<'tcx> {
    /// Returns `true` iff the lifetime projection is mutable
    pub fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        self.projection.mutability(repacker)
    }

    pub fn projection_index(&self, repacker: PlaceRepacker<'_, 'tcx>) -> usize {
        self.projection.index(repacker)
    }

    pub fn direction(&self) -> RegionProjectionMemberDirection {
        self.direction
    }

    pub fn new(
        place: MaybeRemotePlace<'tcx>,
        projection: RegionProjection<'tcx>,
        direction: RegionProjectionMemberDirection,
    ) -> Self {
        Self {
            place,
            projection,
            direction,
        }
    }
}
