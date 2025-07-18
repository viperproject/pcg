use super::AbstractionBlockEdge;
use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, LocalNode, ToBorrowsEdge};
use crate::borrow_pcg::domain::LoopAbstractionOutput;
use crate::borrow_pcg::edge::abstraction::{AbstractionType, LoopAbstractionInput};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate};
use crate::borrow_pcg::has_pcs_elem::{HasPcgElems, LabelRegionProjection, LabelRegionProjectionPredicate, LabelRegionProjectionResult, PlaceLabeller};
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::RegionProjectionLabel;
use crate::pcg::PCGNode;
use crate::rustc_interface::middle::mir::{BasicBlock, Location};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::validity::HasValidityCheck;
use crate::utils::CompilerCtxt;

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct LoopAbstraction<'tcx> {
    pub(crate) edge: AbstractionBlockEdge<'tcx, LoopAbstractionInput<'tcx>, LoopAbstractionOutput<'tcx>>,
    pub(crate) block: BasicBlock,
}

impl<'tcx> LoopAbstraction<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: LoopAbstractionOutput<'tcx>,
        to: LoopAbstractionOutput<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        self.edge.redirect(from, to, ctxt);
        self.assert_validity(ctxt);
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for LoopAbstraction<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> LabelRegionProjectionResult {
        self.edge
            .label_region_projection(projection, label, repacker)
    }
}
impl<'tcx> EdgeData<'tcx> for LoopAbstraction<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.edge.blocks_node(node, repacker)
    }
    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        repacker: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PCGNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_nodes(repacker)
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        repacker: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.edge.blocked_by_nodes(repacker)
    }
}

impl<'tcx> LabelEdgePlaces<'tcx> for LoopAbstraction<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge.label_blocked_by_places(predicate, labeller, ctxt)
    }
}
impl<'tcx> HasValidityCheck<'tcx> for LoopAbstraction<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.edge.check_validity(ctxt)
    }
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for LoopAbstraction<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        format!(
            "Loop({:?}): {}",
            self.block,
            self.edge.to_short_string(ctxt)
        )
    }
}

impl<'tcx, T> HasPcgElems<T> for LoopAbstraction<'tcx>
where
    AbstractionBlockEdge<'tcx, LoopAbstractionInput<'tcx>, LoopAbstractionOutput<'tcx>>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut T> {
        self.edge.pcg_elems()
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for LoopAbstraction<'tcx> {
    fn to_borrow_pcg_edge(self, path_conditions: PathConditions) -> BorrowPcgEdge<'tcx> {
        BorrowPcgEdge::new(
            BorrowPcgEdgeKind::Abstraction(AbstractionType::Loop(self)),
            path_conditions,
        )
    }
}

impl<'tcx> LoopAbstraction<'tcx> {
    pub(crate) fn new(
        edge: AbstractionBlockEdge<'tcx, LoopAbstractionInput<'tcx>, LoopAbstractionOutput<'tcx>>,
        block: BasicBlock,
    ) -> Self {
        Self { edge, block }
    }

    pub(crate) fn location(&self) -> Location {
        Location {
            block: self.block,
            statement_index: 0,
        }
    }
}
