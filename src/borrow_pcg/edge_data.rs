use crate::pcg::PCGNode;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::utils::CompilerCtxt;

use super::borrow_pcg_edge::{BlockedNode, LocalNode};

/// A trait for data that represents a hyperedge in the Borrow PCG.
pub trait EdgeData<'tcx> {
    /// For an edge A -> B, this returns the set of nodes A. In general, the capabilities
    /// of nodes B are obtained from these nodes.
    fn blocked_nodes<'slf, C: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> Box<dyn std::iter::Iterator<Item = PCGNode<'tcx>> + 'slf>
    where
        'tcx: 'slf;

    /// For an edge A -> B, this returns the set of nodes B. In general, these nodes
    /// obtain their capabilities from the nodes A.
    fn blocked_by_nodes<'slf, 'mir: 'slf, C: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, C>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir;

    fn blocks_node<C: Copy>(
        &self,
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        self.blocked_nodes(ctxt).any(|n| n == node)
    }

    fn is_blocked_by<C: Copy>(
        &self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        self.blocked_by_nodes(ctxt).any(|n| n == node)
    }
}

#[macro_export]
macro_rules! edgedata_enum {
    (
        $enum_name:ident < $tcx:lifetime >,
        $( $variant_name:ident($inner_type:ty) ),+ $(,)?
    ) => {
        impl<$tcx> $crate::borrow_pcg::edge_data::EdgeData<$tcx> for $enum_name<$tcx> {
            fn blocked_nodes<'slf, C: Copy + 'slf>(
                &'slf self,
                repacker: CompilerCtxt<'_, $tcx, C>,
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

            fn blocked_by_nodes<'slf, 'mir: 'slf, C: Copy + 'slf>(
                &'slf self,
                repacker: CompilerCtxt<'mir, $tcx, C>,
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

            fn blocks_node<C: Copy>(
                &self,
                node: BlockedNode<'tcx>,
                repacker: CompilerCtxt<'_, $tcx, C>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocks_node(node, repacker),
                    )+
                }
            }

            fn is_blocked_by<C: Copy>(
                &self,
                node: LocalNode<'tcx>,
                repacker: CompilerCtxt<'_, $tcx, C>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.is_blocked_by(node, repacker),
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

        impl<$tcx> $crate::borrow_pcg::has_pcs_elem::MakePlaceOld<$tcx> for $enum_name<$tcx> {
            fn make_place_old(
                &mut self,
                place: $crate::utils::Place<'tcx>,
                latest: &$crate::borrow_pcg::latest::Latest<'tcx>,
                repacker: CompilerCtxt<'_, 'tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.make_place_old(place, latest, repacker),
                    )+
                }
            }
        }

        impl<$tcx> $crate::borrow_pcg::has_pcs_elem::LabelRegionProjection<$tcx> for $enum_name<$tcx> {
            fn label_region_projection(
                &mut self,
                projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
                location: Option<$crate::borrow_pcg::region_projection::RegionProjectionLabel>,
                repacker: CompilerCtxt<'_, 'tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_region_projection(projection, location, repacker),
                    )+
                }
            }
        }

        impl<$tcx> HasValidityCheck<$tcx> for $enum_name<$tcx> {
            fn check_validity<C: Copy>(
                &self,
                repacker: CompilerCtxt<'_, 'tcx, C>,
            ) -> Result<(), String> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.check_validity(repacker),
                    )+
                }
            }
        }

        impl<$tcx> DisplayWithCompilerCtxt<$tcx> for $enum_name<$tcx> {
            fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.to_short_string(repacker),
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
