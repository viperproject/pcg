use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge_data::EdgeData,
        has_pcs_elem::{default_make_place_old, HasPcgElems, LabelRegionProjection, MakePlaceOld},
        latest::Latest,
        region_projection::{LocalRegionProjection, RegionProjection, RegionProjectionLabel},
    },
    pcg::{PCGNode, PCGNodeLike},
    pcg_validity_assert,
    rustc_interface::data_structures::fx::FxHashSet,
    utils::{
        display::DisplayWithCompilerCtxt, maybe_old::MaybeOldPlace, redirect::MaybeRedirected,
        validity::HasValidityCheck, CompilerCtxt, Place,
    },
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowFlowEdge<'tcx> {
    long: RegionProjection<'tcx>,
    short: MaybeRedirected<LocalRegionProjection<'tcx>>,
    pub(crate) kind: BorrowFlowEdgeKind,
}

impl<'tcx> LabelRegionProjection<'tcx> for BorrowFlowEdge<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = self
            .long
            .label_region_projection(projection, label, repacker);
        changed |= self
            .short
            .label_region_projection(projection, label, repacker);
        changed
    }
}

impl<'tcx> MakePlaceOld<'tcx> for BorrowFlowEdge<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for BorrowFlowEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut elems = self.long.pcg_elems();
        elems.extend(self.short.pcg_elems());
        elems
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for BorrowFlowEdge<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "{} -> {}",
            self.long.to_short_string(repacker),
            self.short.to_short_string(repacker)
        )
    }
}

impl<'tcx> EdgeData<'tcx> for BorrowFlowEdge<'tcx> {
    fn blocks_node<C: Copy>(
        &self,
        node: PCGNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        self.long.to_pcg_node(repacker) == node
    }

    fn blocked_nodes<'slf, C: Copy + 'slf>(
        &'slf self,
        _repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Box<dyn Iterator<Item = PCGNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(self.long.into()))
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, C: Copy + 'slf>(
        &'slf self,
        _repacker: CompilerCtxt<'mir, 'tcx, C>,
    ) -> Box<dyn Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
    {
        Box::new(std::iter::once(self.short.effective().into()))
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowFlowEdge<'tcx> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        self.long.check_validity(repacker)?;
        self.short.check_validity(repacker)?;
        Ok(())
    }
}

impl<'tcx> BorrowFlowEdge<'tcx> {
    pub(crate) fn redirect(&mut self, from: LocalNode<'tcx>, to: LocalNode<'tcx>) {
        if let PCGNode::RegionProjection(rp) = from {
            self.short.redirect(rp, to.try_into().unwrap());
        }
    }

    pub(crate) fn new(
        long: RegionProjection<'tcx>,
        short: LocalRegionProjection<'tcx>,
        kind: BorrowFlowEdgeKind,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        pcg_validity_assert!(long.to_pcg_node(repacker) != short.to_pcg_node(repacker));
        Self {
            long,
            short: short.into(),
            kind,
        }
    }

    pub fn long(&self) -> RegionProjection<'tcx> {
        self.long
    }

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
    CopySharedRef,
    Move,
    HavocRegion,
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
            BorrowFlowEdgeKind::CopySharedRef => write!(f, "CopySharedRef"),
            BorrowFlowEdgeKind::HavocRegion => write!(f, "HavocRegion"),
            BorrowFlowEdgeKind::Move => write!(f, "Move"),
        }
    }
}
