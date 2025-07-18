//! Borrow-flow edges
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            HasPcgElems, LabelPlace, LabelRegionProjection, LabelRegionProjectionPredicate,
            LabelRegionProjectionResult, PlaceLabeller,
        },
        region_projection::{LocalRegionProjection, RegionProjection, RegionProjectionLabel},
    },
    pcg::{PCGNode, PCGNodeLike},
    pcg_validity_assert,
    utils::{
        display::DisplayWithCompilerCtxt,
        maybe_old::MaybeOldPlace,
        redirect::{MaybeRedirected, RedirectResult},
        validity::HasValidityCheck,
        CompilerCtxt,
    },
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowFlowEdge<'tcx> {
    long: RegionProjection<'tcx>,
    short: MaybeRedirected<LocalRegionProjection<'tcx>>,
    pub(crate) kind: BorrowFlowEdgeKind,
}

impl<'tcx> LabelEdgePlaces<'tcx> for BorrowFlowEdge<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.long.label_place(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.short.label_place(predicate, labeller, ctxt)
    }
}

impl<'tcx> LabelPlace<'tcx> for LocalRegionProjection<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.base.label_place(predicate, labeller, ctxt)
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for BorrowFlowEdge<'tcx> {
    fn label_region_projection(
        &mut self,
        predicate: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelRegionProjectionResult {
        tracing::debug!(
            "Labeling region projection: {} (predicate: {:?}, label: {:?})",
            self.to_short_string(ctxt),
            predicate,
            label
        );
        if predicate.matches(self.long, ctxt)
            && predicate.matches(self.short.effective().rebase(), ctxt)
        {
            return LabelRegionProjectionResult::ShouldCollapse;
        }
        let mut changed = self.long.label_region_projection(predicate, label, ctxt);
        changed |= self.short.label_region_projection(predicate, label, ctxt);
        self.assert_validity(ctxt);
        changed
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for BorrowFlowEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut elems = self.long.pcg_elems();
        elems.extend(self.short.pcg_elems());
        elems
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
    fn blocks_node<'slf>(&self, node: PCGNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.long.to_pcg_node(repacker) == node
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        _ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn Iterator<Item = PCGNode<'tcx>> + 'slf>
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
        Box::new(std::iter::once(self.short.effective().into()))
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowFlowEdge<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.long.check_validity(ctxt)?;
        self.short.check_validity(ctxt)?;
        if self.long.to_pcg_node(ctxt) == self.short.effective().to_pcg_node(ctxt) {
            return Err(format!(
                "BorrowFlowEdge: long and short are the same node: {}",
                self.to_short_string(ctxt)
            ));
        }
        Ok(())
    }
}

impl<'tcx> BorrowFlowEdge<'tcx> {
    /// Returns true if the edge could be redirected, false if it would create a self edge.
    pub(crate) fn redirect(
        &mut self,
        from: LocalNode<'tcx>,
        to: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> RedirectResult {
        if let PCGNode::RegionProjection(rp) = from {
            self.short.redirect(rp, to.try_into().unwrap());
        }
        if self.long.to_pcg_node(ctxt) == self.short.effective().to_pcg_node(ctxt) {
            RedirectResult::SelfRedirect
        } else {
            RedirectResult::Redirect
        }
    }

    pub(crate) fn new(
        long: RegionProjection<'tcx>,
        short: LocalRegionProjection<'tcx>,
        kind: BorrowFlowEdgeKind,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        pcg_validity_assert!(long.to_pcg_node(ctxt) != short.to_pcg_node(ctxt));
        Self {
            long,
            short: short.into(),
            kind,
        }
    }

    /// The blocked lifetime projection. Intuitively, it must outlive the `short()` projection.
    pub fn long(&self) -> RegionProjection<'tcx> {
        self.long
    }

    /// The blocking lifetime projection. Intuitively, it must die before the `long()` projection.
    pub fn short(&self) -> LocalRegionProjection<'tcx> {
        self.short.effective()
    }

    pub fn kind(&self) -> BorrowFlowEdgeKind {
        self.kind
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum BorrowFlowEdgeKind {
    /// Region projection edge resulting due to contracting a place. For
    /// example, if the type of `x.t` is `&'a mut T` and there is a borrow `x.t
    /// = &mut y`, and we need to contract to `x`, then we need to replace the
    /// borrow edge with an edge `{y} -> {x↓'a}` of this kind.
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
    /// `lifetimes_equal` is true if the lifetimes are equal, false otherwise.
    BorrowOutlives {
        regions_equal: bool,
    },
    InitialBorrows,
    CopyRef,
    Move,
    Future,
    Other, // TODO
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
            BorrowFlowEdgeKind::Other => write!(f, "Other"),
        }
    }
}
