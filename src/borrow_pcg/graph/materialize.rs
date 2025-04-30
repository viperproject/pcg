use derive_more::From;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeLike, BorrowPCGEdgeRef},
        edge::kind::BorrowPcgEdgeKind,
    },
    pcg::PCGNode,
    utils::CompilerCtxt,
};

use super::BorrowsGraph;

#[derive(Clone, Copy)]
pub(crate) struct AliasEdge<'tcx> {
    pub(crate) blocked_place: PCGNode<'tcx>,
    pub(crate) blocking_place: PCGNode<'tcx>,
}

#[derive(Clone, Copy)]
pub(crate) enum SyntheticEdge<'tcx> {
    Alias(AliasEdge<'tcx>),
}

#[derive(From)]
pub(crate) enum MaterializedEdge<'tcx, 'graph> {
    Real(BorrowPCGEdgeRef<'tcx, 'graph>),
    Synthetic(SyntheticEdge<'tcx>),
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn materialized_edges<'graph, 'mir>(
        &'graph self,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> Vec<MaterializedEdge<'tcx, 'graph>> {
        let mut result = Vec::new();
        for edge in self.edges() {
            result.push(edge.into());
            if let BorrowPcgEdgeKind::Borrow(edge) = edge.kind() {
                if self.contains(edge.deref_place(repacker), repacker) {
                    result.push(MaterializedEdge::Synthetic(SyntheticEdge::Alias(
                        AliasEdge {
                            blocked_place: edge.blocked_place().into(),
                            blocking_place: edge.deref_place(repacker).into(),
                        },
                    )));
                }
            }
        }
        result
    }
}
