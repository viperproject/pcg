use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::borrow_pcg_expansion::BorrowPcgExpansion;
use crate::borrow_pcg::edge::abstraction::AbstractionType;
use crate::borrow_pcg::edge::borrow::BorrowEdge;
use crate::utils::CompilerCtxt;

use super::borrow::RemoteBorrow;
use super::outlives::BorrowFlowEdge;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowPcgEdgeKind<'tcx> {
    Borrow(BorrowEdge<'tcx>),
    BorrowPcgExpansion(BorrowPcgExpansion<'tcx>),
    Abstraction(AbstractionType<'tcx>),
    BorrowFlow(BorrowFlowEdge<'tcx>),
}

impl<'tcx> From<RemoteBorrow<'tcx>> for BorrowPcgEdgeKind<'tcx> {
    fn from(borrow: RemoteBorrow<'tcx>) -> Self {
        BorrowPcgEdgeKind::Borrow(BorrowEdge::Remote(borrow))
    }
}

impl<'tcx> BorrowPcgEdgeKind<'tcx> {
    pub(crate) fn is_shared_borrow(&self, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        match self {
            BorrowPcgEdgeKind::Borrow(reborrow) => !reborrow.is_mut(repacker),
            _ => false,
        }
    }

    pub(crate) fn redirect(&mut self, from: LocalNode<'tcx>, to: LocalNode<'tcx>) {
        match self {
            BorrowPcgEdgeKind::BorrowFlow(edge) => edge.redirect(from, to),
            other => panic!("Cannot redirect this edge kind: {other:?}"),
        }
    }
}
