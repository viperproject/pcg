use crate::borrow_pcg::borrow_pcg_expansion::BorrowPCGExpansion;
use crate::borrow_pcg::edge::abstraction::AbstractionType;
use crate::borrow_pcg::edge::borrow::BorrowEdge;
use crate::borrow_pcg::has_pcs_elem::HasPcsElems;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::borrow_pcg::edge::block::BlockEdge;
use crate::utils::display::DisplayWithRepacker;
use crate::utils::PlaceRepacker;
use crate::utils::validity::HasValidityCheck;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowPCGEdgeKind<'tcx> {
    Borrow(BorrowEdge<'tcx>),
    BorrowPCGExpansion(BorrowPCGExpansion<'tcx>),
    Abstraction(AbstractionType<'tcx>),
    Block(BlockEdge<'tcx>),
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowPCGEdgeKind<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        match self {
            BorrowPCGEdgeKind::Borrow(borrow) => borrow.check_validity(repacker),
            BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => expansion.check_validity(repacker),
            BorrowPCGEdgeKind::Abstraction(abstraction) => abstraction.check_validity(repacker),
            BorrowPCGEdgeKind::Block(member) => member.check_validity(repacker),
        }
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for BorrowPCGEdgeKind<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match self {
            BorrowPCGEdgeKind::Borrow(borrow) => borrow.to_short_string(repacker),
            BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => expansion.to_short_string(repacker),
            BorrowPCGEdgeKind::Abstraction(abstraction) => abstraction.to_short_string(repacker),
            BorrowPCGEdgeKind::Block(member) => member.to_short_string(repacker),
        }
    }
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx>> for BorrowPCGEdgeKind<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        match self {
            BorrowPCGEdgeKind::Block(member) => member.pcs_elems(),
            _ => vec![],
        }
    }
}

impl<'tcx, T> HasPcsElems<T> for BorrowPCGEdgeKind<'tcx>
where
    BorrowEdge<'tcx>: HasPcsElems<T>,
    BlockEdge<'tcx>: HasPcsElems<T>,
    BorrowPCGExpansion<'tcx>: HasPcsElems<T>,
    AbstractionType<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        match self {
            BorrowPCGEdgeKind::Block(member) => member.pcs_elems(),
            BorrowPCGEdgeKind::Borrow(reborrow) => reborrow.pcs_elems(),
            BorrowPCGEdgeKind::BorrowPCGExpansion(deref_expansion) => deref_expansion.pcs_elems(),
            BorrowPCGEdgeKind::Abstraction(abstraction_edge) => abstraction_edge.pcs_elems(),
        }
    }
}

impl BorrowPCGEdgeKind<'_> {
    pub(crate) fn is_shared_borrow(&self) -> bool {
        match self {
            BorrowPCGEdgeKind::Borrow(reborrow) => !reborrow.is_mut(),
            _ => false,
        }
    }
}
