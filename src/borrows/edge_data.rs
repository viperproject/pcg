use crate::combined_pcs::PCGNode;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::utils::PlaceRepacker;

use super::borrow_pcg_edge::{BlockedNode, LocalNode};

/// A trait for data that represents a hyperedge in the Borrow PCG.
pub trait EdgeData<'tcx> {
    /// For an edge A -> B, this returns the set of nodes A. In general, the capabilities
    /// of nodes B are obtained from these nodes.
    fn blocked_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>>;

    /// For an edge A -> B, this returns the set of nodes B. In general, these nodes
    /// obtain their capabilities from the nodes A.
    fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>>;

    /// True iff this is an edge from the owned PCG to the borrow PCG, e.g. x -> *x iff x is a reference type
    fn is_owned_expansion(&self) -> bool;

    fn blocks_node(&self, node: BlockedNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.blocked_nodes(repacker).contains(&node)
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.blocked_by_nodes(repacker).contains(&node)
    }
}

#[macro_export]
macro_rules! edgedata_enum {
    (
        $enum_name:ident < $tcx:lifetime >,
        $( $variant_name:ident($inner_type:ty) ),+ $(,)?
    ) => {
        impl<$tcx> crate::borrows::edge_data::EdgeData<$tcx> for $enum_name<$tcx> {
            fn blocked_nodes(&self, repacker: PlaceRepacker<'_, $tcx>) -> FxHashSet<PCGNode<'tcx>> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_nodes(repacker),
                    )+
                }
            }

            fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, $tcx>) -> FxHashSet<crate::borrows::borrow_pcg_edge::LocalNode<'tcx>> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_by_nodes(repacker),
                    )+
                }
            }

            fn blocks_node(&self, node: BlockedNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool { match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocks_node(node, repacker),
                    )+
                }
            }

            fn is_blocked_by(&self, node: LocalNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool { match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.is_blocked_by(node, repacker),
                    )+
                }
            }

            fn is_owned_expansion(&self) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.is_owned_expansion(),
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
    }
}
