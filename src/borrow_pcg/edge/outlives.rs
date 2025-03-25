use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge_data::EdgeData,
        has_pcs_elem::{default_make_place_old, HasPcgElems, MakePlaceOld},
        latest::Latest,
        region_projection::{LocalRegionProjection, RegionProjection},
    },
    combined_pcs::{PCGNode, PCGNodeLike},
    pcg_validity_assert,
    rustc_interface::data_structures::fx::FxHashSet,
    utils::{
        display::DisplayWithRepacker, maybe_old::MaybeOldPlace, validity::HasValidityCheck, Place,
        PlaceRepacker,
    },
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct OutlivesEdge<'tcx> {
    long: RegionProjection<'tcx>,
    short: LocalRegionProjection<'tcx>,
    pub(crate) kind: OutlivesEdgeKind,
}

impl<'tcx> MakePlaceOld<'tcx> for OutlivesEdge<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for OutlivesEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut elems = self.long.pcg_elems();
        elems.extend(self.short.pcg_elems());
        elems
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for OutlivesEdge<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "{} -> {}",
            self.long.to_short_string(repacker),
            self.short.to_short_string(repacker)
        )
    }
}

impl<'tcx> EdgeData<'tcx> for OutlivesEdge<'tcx> {
    fn blocks_node(&self, node: PCGNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.long.to_pcg_node(repacker) == node
    }

    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        std::iter::once(self.long.into()).collect()
    }

    fn blocked_by_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        std::iter::once(self.short.into()).collect()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for OutlivesEdge<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.long.check_validity(repacker)?;
        self.short.check_validity(repacker)?;
        Ok(())
    }
}

impl<'tcx> OutlivesEdge<'tcx> {
    pub(crate) fn new(
        long: RegionProjection<'tcx>,
        short: LocalRegionProjection<'tcx>,
        kind: OutlivesEdgeKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        pcg_validity_assert!(long.to_pcg_node(repacker) != short.to_pcg_node(repacker));
        Self { long, short, kind }
    }

    pub(crate) fn long(&self) -> RegionProjection<'tcx> {
        self.long
    }

    pub(crate) fn short(&self) -> LocalRegionProjection<'tcx> {
        self.short
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum OutlivesEdgeKind {
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
    /// `toplevel` is true for edges to x↓'x, false otherwise.
    BorrowOutlives {
        toplevel: bool,
    },
    InitialBorrows,
    CopySharedRef,
    HavocRegion
}

impl std::fmt::Display for OutlivesEdgeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OutlivesEdgeKind::Aggregate {
                        field_idx,
                        target_rp_index,
                    } => write!(f, "Aggregate({field_idx}, {target_rp_index})"),
            OutlivesEdgeKind::ConstRef => write!(f, "ConstRef"),
            OutlivesEdgeKind::BorrowOutlives { toplevel } => {
                        write!(f, "BorrowOutlives({toplevel})")
                    }
            OutlivesEdgeKind::InitialBorrows => write!(f, "InitialBorrows"),
            OutlivesEdgeKind::CopySharedRef => write!(f, "CopySharedRef"),
            OutlivesEdgeKind::HavocRegion => write!(f, "HavocRegion"),
        }
    }
}
