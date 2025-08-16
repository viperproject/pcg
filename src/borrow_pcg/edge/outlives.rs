//! Borrow-flow edges
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlaceWithContext, PlaceLabeller,
        },
        region_projection::{LifetimeProjection, LifetimeProjectionLabel, LocalLifetimeProjection},
    },
    pcg::{PCGNodeLike, PcgNode},
    pcg_validity_assert,
    utils::{
        CompilerCtxt, HasCompilerCtxt, display::DisplayWithCompilerCtxt, validity::HasValidityCheck,
    },
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowFlowEdge<'tcx> {
    long: LifetimeProjection<'tcx>,
    short: LocalLifetimeProjection<'tcx>,
    pub(crate) kind: BorrowFlowEdgeKind,
}

impl<'tcx> LabelEdgePlaces<'tcx> for BorrowFlowEdge<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.long
            .label_place_with_context(predicate, labeller, LabelNodeContext::Other, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.short
            .label_place_with_context(predicate, labeller, LabelNodeContext::Other, ctxt)
    }
}

impl<'tcx> LabelLifetimeProjection<'tcx> for BorrowFlowEdge<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        tracing::debug!(
            "Labeling region projection: {} (predicate: {:?}, label: {:?})",
            self.to_short_string(ctxt),
            predicate,
            label
        );
        if predicate.matches(self.long, ctxt) && predicate.matches(self.short.rebase(), ctxt) {
            return LabelLifetimeProjectionResult::ShouldCollapse;
        }
        let mut changed = self.long.label_lifetime_projection(predicate, label, ctxt);
        changed |= self.short.label_lifetime_projection(predicate, label, ctxt);
        self.assert_validity(ctxt);
        changed
    }
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for BorrowFlowEdge<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        format!(
            "{} -> {}",
            self.long.to_short_string(ctxt),
            self.short.to_short_string(ctxt)
        )
    }
}

impl<'tcx> EdgeData<'tcx> for BorrowFlowEdge<'tcx> {
    fn blocks_node<'slf>(&self, node: PcgNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.long.to_pcg_node(repacker) == node
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        _ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(self.long.into()))
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy>(
        &'slf self,
        _repacker: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
    {
        Box::new(std::iter::once(self.short.into()))
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowFlowEdge<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.long.check_validity(ctxt)?;
        self.short.check_validity(ctxt)?;
        if self.long.to_pcg_node(ctxt) == self.short.to_pcg_node(ctxt) {
            return Err(format!(
                "BorrowFlowEdge: long and short are the same node: {}",
                self.to_short_string(ctxt)
            ));
        }
        Ok(())
    }
}

impl<'tcx> BorrowFlowEdge<'tcx> {
    pub(crate) fn new<'a>(
        long: LifetimeProjection<'tcx>,
        short: LocalLifetimeProjection<'tcx>,
        kind: BorrowFlowEdgeKind,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        pcg_validity_assert!(long.to_pcg_node(ctxt.ctxt()) != short.to_pcg_node(ctxt.ctxt()));
        Self { long, short, kind }
    }

    /// The blocked lifetime projection. Intuitively, it must outlive the `short()` projection.
    pub fn long(&self) -> LifetimeProjection<'tcx> {
        self.long
    }

    /// The blocking lifetime projection. Intuitively, it must die before the `long()` projection.
    pub fn short(&self) -> LocalLifetimeProjection<'tcx> {
        self.short
    }

    pub fn kind(&self) -> BorrowFlowEdgeKind {
        self.kind
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum BorrowFlowEdgeKind {
    /// Indicates that the borrow flows to the `target_rp_index`th region
    /// projection of the `field_idx`th field of the aggregate.
    ///
    /// Introduced in the following two cases:
    /// 1. Collapsing an owned place: edges flow from the (labelled) expansions
    ///    of the place to the current base
    /// 2. Assigning an aggregate (e.g. `x = Aggregate(a, b)`): edges flow from
    ///    the (labelled) arguments to the rvalue to lifetime projections of `x`
    ///
    /// TODO: Perhaps a different kind for the 1st case? We don't need this metadata I think
    Aggregate {
        field_idx: usize,
        target_rp_index: usize,
    },
    /// Connects a region projection from a constant to some PCG node. For
    /// example `let x: &'x C = c;` where `c` is a constant of type `&'c C`, then
    /// an edge `{c↓'c} -> {x↓'x}` of this kind is created.
    ConstRef,
    /// For a borrow `let x: &'x T<'b> = &y`, where y is of typ T<'a>, an edge generated
    /// for `{y|'a} -> {x|'b}` of this kind is created if 'a outlives 'b.
    ///
    BorrowOutlives {
        /// If true, the lifetimes are equal (mutually outlive each other),
        /// false otherwise.
        ///
        /// This field is somewhat redundant because the equality can be queried
        /// by the borrow checker based on the regions of the long and short
        /// endpoints. However, it is useful for clients that may not have access
        /// to the borrow checker (e.g. visualization tools).
        regions_equal: bool,
    },
    InitialBorrows,
    CopyRef,
    Move,
    Future,
}

impl std::fmt::Display for BorrowFlowEdgeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BorrowFlowEdgeKind::Aggregate {
                field_idx,
                target_rp_index,
            } => write!(f, "Aggregate({field_idx}, {target_rp_index})"),
            BorrowFlowEdgeKind::ConstRef => write!(f, "ConstRef"),
            BorrowFlowEdgeKind::BorrowOutlives {
                regions_equal: lifetimes_equal,
            } => {
                if *lifetimes_equal {
                    write!(f, "equals")
                } else {
                    write!(f, "outlives")
                }
            }
            BorrowFlowEdgeKind::InitialBorrows => write!(f, "InitialBorrows"),
            BorrowFlowEdgeKind::CopyRef => write!(f, "CopyRef"),
            BorrowFlowEdgeKind::Move => write!(f, "Move"),
            BorrowFlowEdgeKind::Future => write!(f, "Future"),
        }
    }
}
