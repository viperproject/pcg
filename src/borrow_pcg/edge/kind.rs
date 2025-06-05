use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::borrow_pcg_expansion::BorrowPcgExpansion;
use crate::borrow_pcg::domain::AbstractionOutputTarget;
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
    #[must_use]
    pub(crate) fn redirect(
        &mut self,
        from: LocalNode<'tcx>,
        to: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            BorrowPcgEdgeKind::BorrowFlow(edge) => edge.redirect(from, to, ctxt),
            BorrowPcgEdgeKind::Abstraction(edge) => {
                let from: Option<AbstractionOutputTarget<'tcx>> = from.try_into().ok();
                let to: Option<AbstractionOutputTarget<'tcx>> = to.try_into().ok();
                if let Some(from) = from
                    && let Some(to) = to
                {
                    edge.redirect(from, to, ctxt);
                }
                // TODO
                true
            }
            other => panic!("Cannot redirect this edge kind: {other:?}"),
        }
    }
}
