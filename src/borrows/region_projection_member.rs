use std::collections::BTreeSet;

use crate::rustc_interface::{ast::Mutability, data_structures::fx::FxHashSet};
use crate::utils::PlaceRepacker;

use super::borrow_pcg_edge::{LocalNode, PCGNode};
use super::coupling_graph_constructor::Coupled;
use super::edge_data::EdgeData;
use super::{
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
    /// *Coupled* region projections;
    pub projections: Coupled<RegionProjection<'tcx>>,
    direction: RegionProjectionMemberDirection,
}

impl<'tcx> EdgeData<'tcx> for RegionProjectionMember<'tcx> {
    fn blocked_by_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        match self.direction {
            RegionProjectionMemberDirection::ProjectionBlocksPlace => self
                .projections
                .iter()
                .map(|p| LocalNode::RegionProjection(*p))
                .collect(),
            RegionProjectionMemberDirection::PlaceBlocksProjection => {
                vec![LocalNode::Place(self.place.as_local_place().unwrap())]
                    .into_iter()
                    .collect()
            }
        }
    }

    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        match self.direction {
            RegionProjectionMemberDirection::ProjectionBlocksPlace => {
                vec![self.place.into()].into_iter().collect()
            }
            RegionProjectionMemberDirection::PlaceBlocksProjection => {
                self.projections.iter().map(|p| (*p).into()).collect()
            }
        }
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx>> for RegionProjectionMember<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        self.projections.iter_mut().collect()
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjectionMember<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut vec = self.place.pcs_elems();
        vec.extend(self.projections.iter_mut().flat_map(|p| p.pcs_elems()));
        vec
    }
}

impl<'tcx> RegionProjectionMember<'tcx> {
    /// Returns `true` iff the lifetime projections are mutable
    pub fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        self.projections.mutability(repacker)
    }

    pub fn direction(&self) -> RegionProjectionMemberDirection {
        self.direction
    }

    pub fn new(
        place: MaybeRemotePlace<'tcx>,
        projections: Coupled<RegionProjection<'tcx>>,
        direction: RegionProjectionMemberDirection,
    ) -> Self {
        Self {
            place,
            projections,
            direction,
        }
    }
}
