use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike},
        edge::{
            kind::BorrowPcgEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
        region_projection::{LocalRegionProjection, RegionProjection, RegionProjectionLabel},
    },
    pcg::PcgError,
    pcg_validity_assert,
};

use super::PcgVisitor;

impl<'pcg, 'mir, 'tcx> PcgVisitor<'pcg, 'mir, 'tcx> {
    pub(crate) fn add_and_update_placeholder_edges(
        &mut self,
        labelled_rp: LocalRegionProjection<'tcx>,
        expansion_rps: &[RegionProjection<'tcx>],
        context: &str,
    ) -> Result<(), PcgError> {
        if expansion_rps.is_empty() {
            return Ok(());
        }
        pcg_validity_assert!(matches!(
            labelled_rp.label(),
            Some(RegionProjectionLabel::Location(_))
        ));
        let future_rp = labelled_rp.with_placeholder_label(self.ctxt);
        self.record_and_apply_action(
            BorrowPcgAction::add_edge(
                BorrowPcgEdge::new(
                    BorrowFlowEdge::new(
                        labelled_rp.into(),
                        future_rp.into(),
                        BorrowFlowEdgeKind::UpdateNestedRefs,
                        self.ctxt,
                    )
                    .into(),
                    self.pcg.borrow.path_conditions.clone(),
                ),
                format!("{}: placeholder bookkeeping", context),
                false,
            )
            .into(),
        )?;
        for expansion_rp in expansion_rps {
            self.record_and_apply_action(
                BorrowPcgAction::add_edge(
                    BorrowPcgEdge::new(
                        BorrowFlowEdge::new(
                            *expansion_rp,
                            future_rp.into(),
                            BorrowFlowEdgeKind::UpdateNestedRefs,
                            self.ctxt,
                        )
                        .into(),
                        self.pcg.borrow.path_conditions.clone(),
                    ),
                    format!("{}: placeholder bookkeeping", context),
                    false,
                )
                .into(),
            )?;
        }
        let to_replace = self
            .pcg
            .borrow
            .edges_blocking(labelled_rp.into(), self.ctxt)
            .into_iter()
            .filter_map(|edge| {
                if let BorrowPcgEdgeKind::BorrowFlow(bf_edge) = edge.kind {
                    if bf_edge.kind == BorrowFlowEdgeKind::UpdateNestedRefs
                        && bf_edge.short() != future_rp.into()
                    {
                        return Some((
                            edge.to_owned_edge(),
                            BorrowPcgEdge::new(
                                BorrowFlowEdge::new(
                                    future_rp.into(),
                                    bf_edge.short(),
                                    BorrowFlowEdgeKind::UpdateNestedRefs,
                                    self.ctxt,
                                )
                                .into(),
                                edge.conditions.clone(),
                            ),
                        ));
                    }
                }
                None
            })
            .collect::<Vec<_>>();
        for (to_remove, to_insert) in to_replace {
            self.record_and_apply_action(
                BorrowPcgAction::remove_edge(to_remove, "placeholder bookkeeping").into(),
            )?;
            self.record_and_apply_action(
                BorrowPcgAction::add_edge(to_insert, "placeholder bookkeeping", false).into(),
            )?;
        }
        Ok(())
    }
}
