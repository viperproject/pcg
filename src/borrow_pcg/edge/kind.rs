//! Describes the kind of Borrow PCG edges
use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::borrow_pcg_expansion::BorrowPcgExpansion;
use crate::borrow_pcg::domain::AbstractionOutputTarget;
use crate::borrow_pcg::edge::abstraction::AbstractionType;
use crate::borrow_pcg::edge::borrow::BorrowEdge;
use crate::utils::redirect::RedirectResult;
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
    pub(crate) fn is_edge_to_future_node(&self) -> bool {
        match self {
            BorrowPcgEdgeKind::BorrowFlow(edge) => edge.short().is_placeholder(),
            _ => false,
        }
    }

    #[allow(unused)]
    pub(crate) fn could_mutate(&self, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        match self {
            BorrowPcgEdgeKind::Borrow(borrow) => borrow.is_mut(repacker),
            BorrowPcgEdgeKind::BorrowFlow(edge) => edge.is_mut(repacker),
            _ => true,
        }
    }

    pub(crate) fn is_shared_borrow(&self, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        match self {
            BorrowPcgEdgeKind::Borrow(reborrow) => !reborrow.is_mut(repacker),
            _ => false,
        }
    }

    /// Returns true if the edge could be redirected, false if it would create a self edge.
    pub(crate) fn redirect(
        &mut self,
        from: LocalNode<'tcx>,
        to: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> RedirectResult {
        match self {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => expansion.redirect(from, to, ctxt),
            BorrowPcgEdgeKind::BorrowFlow(edge) => edge.redirect(from, to, ctxt),
            BorrowPcgEdgeKind::Abstraction(edge) => {
                let from: AbstractionOutputTarget<'tcx> = from.into();
                let to: AbstractionOutputTarget<'tcx> = to.into();
                edge.redirect(from, to, ctxt);
                // TODO
                RedirectResult::Redirect
            }
            other => panic!("Cannot redirect this edge kind: {other:?}"),
        }
    }
}
