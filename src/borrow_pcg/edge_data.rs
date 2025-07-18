use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::has_pcs_elem::PlaceLabeller;
use crate::pcg::PCGNode;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::{CompilerCtxt, Place};
use crate::rustc_interface::middle::mir::ProjectionElem;

use super::borrow_pcg_edge::{BlockedNode, LocalNode};

/// A trait for data that represents a hyperedge in the Borrow PCG.
pub trait EdgeData<'tcx> {
    /// For an edge A -> B, this returns the set of nodes A. In general, the capabilities
    /// of nodes B are obtained from these nodes.
    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PCGNode<'tcx>> + 'slf>
    where
        'tcx: 'slf;

    /// For an edge A -> B, this returns the set of nodes B. In general, these nodes
    /// obtain their capabilities from the nodes A.
    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir;

    fn blocks_node(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.blocked_nodes(ctxt).any(|n| n == node)
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.blocked_by_nodes(ctxt).any(|n| n == node)
    }

    fn nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PCGNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(
            self.blocked_nodes(ctxt)
                .chain(self.blocked_by_nodes(ctxt).map(|n| n.into())),
        )
    }

    fn references_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.nodes(ctxt).any(|n| match n {
            PCGNode::Place(p) => p.as_current_place() == Some(place),
            PCGNode::RegionProjection(rp) => rp.base.as_current_place() == Some(place),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LabelPlacePredicate<'tcx> {
    Exact(Place<'tcx>),
    PrefixWithoutIndirectionOrPostfix(Place<'tcx>),
    LabelSharedDerefProjections(Place<'tcx>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EdgePredicate {
    All,
    BorrowEdges,
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for LabelPlacePredicate<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            LabelPlacePredicate::PrefixWithoutIndirectionOrPostfix(predicate_place) => {
                predicate_place.to_short_string(ctxt) // As a hack for now so debug output doesn't change
            }
            LabelPlacePredicate::LabelSharedDerefProjections(place) => {
                format!("strict postfix of {}", place.to_short_string(ctxt))
            }
            LabelPlacePredicate::Exact(place) => {
                format!("exact {}", place.to_short_string(ctxt))
            }
        }
    }
}

impl<'tcx> LabelPlacePredicate<'tcx> {
    pub(crate) fn applies_to(&self, candidate: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        match self {
            LabelPlacePredicate::PrefixWithoutIndirectionOrPostfix(predicate_place) => {
                if predicate_place.is_prefix_of(candidate) {
                    true
                } else if candidate.is_prefix_of(*predicate_place) {
                    for p in predicate_place
                        .iter_places(ctxt)
                        .into_iter()
                        .skip(candidate.projection.len() + 1)
                    {
                        if p.parent_place().unwrap().is_ref(ctxt) && p.is_deref() {
                            return false;
                        }
                    }
                    true
                } else {
                    false
                }
            }
            LabelPlacePredicate::LabelSharedDerefProjections(place) => {
                if let Some(iter) = candidate.iter_projections_after(*place, ctxt) {
                    for (place, proj) in iter {
                        if matches!(proj, ProjectionElem::Deref) && place.is_shared_ref(ctxt) {
                            return true;
                        }
                    }
                }
                false
            }
            LabelPlacePredicate::Exact(place) => *place == candidate,
        }
    }
}

pub(crate) trait LabelEdgePlaces<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

macro_rules! edgedata_enum {
    (
        $enum_name:ident < $tcx:lifetime >,
        $( $variant_name:ident($inner_type:ty) ),+ $(,)?
    ) => {
        impl<$tcx> $crate::borrow_pcg::edge_data::EdgeData<$tcx> for $enum_name<$tcx> {
            fn blocked_nodes<'slf, BC: Copy>(
                &'slf self,
                repacker: CompilerCtxt<'_, $tcx, BC>,
            ) -> Box<dyn std::iter::Iterator<Item = PCGNode<'tcx>> + 'slf>
            where
                'tcx: 'slf,
            {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_nodes(repacker),
                    )+
                }
            }

            fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
                &'slf self,
                repacker: CompilerCtxt<'mir, $tcx, BC>,
            ) -> Box<dyn std::iter::Iterator<Item = $crate::borrow_pcg::borrow_pcg_edge::LocalNode<'tcx>> + 'slf>
            where
                'tcx: 'mir,
            {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_by_nodes(repacker),
                    )+
                }
            }

            fn blocks_node<'slf>(
                &self,
                node: BlockedNode<'tcx>,
                repacker: CompilerCtxt<'_, $tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocks_node(node, repacker),
                    )+
                }
            }

            fn is_blocked_by<'slf>(
                &self,
                node: LocalNode<'tcx>,
                repacker: CompilerCtxt<'_, $tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.is_blocked_by(node, repacker),
                    )+
                }
            }
        }

        impl<$tcx> $crate::borrow_pcg::edge_data::LabelEdgePlaces<$tcx> for $enum_name<$tcx> {
            fn label_blocked_places(
                &mut self,
                predicate: &$crate::borrow_pcg::edge_data::LabelPlacePredicate<'tcx>,
                labeller: &impl $crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx>,
                ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_blocked_places(predicate, labeller, ctxt),
                    )+
                }
            }

            fn label_blocked_by_places(
                &mut self,
                predicate: &$crate::borrow_pcg::edge_data::LabelPlacePredicate<'tcx>,
                labeller: &impl $crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx>,
                ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_blocked_by_places(predicate, labeller, ctxt),
                    )+
                }
            }
        }

        $(
            impl<$tcx> From<$inner_type> for $enum_name<$tcx> {
                fn from(inner: $inner_type) -> Self {
                    $enum_name::$variant_name(inner)
                }
            }
        )+

        impl<$tcx> $crate::borrow_pcg::has_pcs_elem::LabelRegionProjection<$tcx> for $enum_name<$tcx> {
            fn label_region_projection(
                &mut self,
                predicate: &$crate::borrow_pcg::has_pcs_elem::LabelRegionProjectionPredicate<'tcx>,
                location: Option<$crate::borrow_pcg::region_projection::RegionProjectionLabel>,
                repacker: CompilerCtxt<'_, 'tcx>,
            ) -> $crate::borrow_pcg::has_pcs_elem::LabelRegionProjectionResult {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_region_projection(predicate, location, repacker),
                    )+
                }
            }
        }

        impl<$tcx> HasValidityCheck<$tcx> for $enum_name<$tcx> {
            fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.check_validity(ctxt),
                    )+
                }
            }
        }

        impl<$tcx, 'a> DisplayWithCompilerCtxt<$tcx, &'a dyn $crate::borrow_checker::BorrowCheckerInterface<'tcx>> for $enum_name<$tcx> {
            fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, &'a dyn $crate::borrow_checker::BorrowCheckerInterface<'tcx>>) -> String {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.to_short_string(ctxt),
                    )+
                }
            }
        }

        impl<'tcx, T> HasPcgElems<T> for $enum_name<$tcx>
            where
                $(
                    $inner_type: HasPcgElems<T>,
                )+
            {
                fn pcg_elems(&mut self) -> Vec<&mut T> {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) => inner.pcg_elems(),
                        )+
                    }
                }
            }
    }
}
pub(crate) use edgedata_enum;
