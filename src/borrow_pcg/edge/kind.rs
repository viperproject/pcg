use crate::borrow_pcg::borrow_pcg_expansion::BorrowPCGExpansion;
use crate::borrow_pcg::edge::abstraction::AbstractionType;
use crate::borrow_pcg::edge::borrow::BorrowEdge;
use crate::utils::PlaceRepacker;

use super::borrow::RemoteBorrow;
use super::outlives::OutlivesEdge;
use super::region_projection_member::RegionProjectionMember;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowPCGEdgeKind<'tcx> {
    Borrow(BorrowEdge<'tcx>),
    BorrowPCGExpansion(BorrowPCGExpansion<'tcx>),
    Abstraction(AbstractionType<'tcx>),
    Outlives(OutlivesEdge<'tcx>),
    RegionProjectionMember(RegionProjectionMember<'tcx>),
}

impl<'tcx> From<RemoteBorrow> for BorrowPCGEdgeKind<'tcx> {
    fn from(borrow: RemoteBorrow) -> Self {
        BorrowPCGEdgeKind::Borrow(BorrowEdge::Remote(borrow))
    }
}

impl <'tcx> BorrowPCGEdgeKind<'tcx> {
    pub(crate) fn is_shared_borrow(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match self {
            BorrowPCGEdgeKind::Borrow(reborrow) => !reborrow.is_mut(repacker),
            _ => false,
        }
    }
}
