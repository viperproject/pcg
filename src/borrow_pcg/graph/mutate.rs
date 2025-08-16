use crate::{
    borrow_pcg::{
        action::LabelPlaceReason,
        borrow_pcg_edge::BorrowPcgEdge,
        has_pcs_elem::PlaceLabeller,
        path_condition::{PathCondition, ValidityConditions},
    },
    rustc_interface::middle::mir::BasicBlock,
    utils::{CompilerCtxt, FilterMutResult, HasBorrowCheckerCtxt, Place},
};

use super::BorrowsGraph;

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn label_place<'a>(
        &mut self,
        place: Place<'tcx>,
        reason: LabelPlaceReason,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.mut_edges(|edge| reason.apply_to_edge(place, edge, labeller, ctxt))
    }

    pub(crate) fn filter_mut_edges<'slf>(
        &'slf mut self,
        mut f: impl FnMut(&mut BorrowPcgEdge<'tcx>) -> FilterMutResult,
    ) -> bool {
        let mut changed = false;
        self.edges = self
            .edges
            .drain()
            .filter_map(|(kind, conditions)| {
                let mut edge = BorrowPcgEdge::new(kind, conditions);
                match f(&mut edge) {
                    FilterMutResult::Changed => {
                        changed = true;
                        Some((edge.kind, edge.conditions))
                    }
                    FilterMutResult::Unchanged => Some((edge.kind, edge.conditions)),
                    FilterMutResult::Remove => None,
                }
            })
            .collect();
        changed
    }

    pub(crate) fn mut_edges<'slf>(
        &'slf mut self,
        mut f: impl FnMut(&mut BorrowPcgEdge<'tcx>) -> bool,
    ) -> bool {
        let mut changed = false;
        self.edges = self
            .edges
            .drain()
            .map(|(kind, conditions)| {
                let mut edge = BorrowPcgEdge::new(kind, conditions);
                if f(&mut edge) {
                    changed = true;
                }
                (edge.kind, edge.conditions)
            })
            .collect();
        changed
    }

    fn mut_edge_conditions(&mut self, mut f: impl FnMut(&mut ValidityConditions) -> bool) -> bool {
        let mut changed = false;
        for (_, conditions) in self.edges.iter_mut() {
            if f(conditions) {
                changed = true;
            }
        }
        changed
    }

    pub(crate) fn filter_for_path(&mut self, path: &[BasicBlock], ctxt: CompilerCtxt<'_, 'tcx>) {
        self.edges
            .retain(|_, conditions| conditions.valid_for_path(path, ctxt.body()));
    }

    pub(crate) fn add_path_condition(
        &mut self,
        pc: PathCondition,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.mut_edge_conditions(|conditions| conditions.insert(pc, ctxt.body()))
    }

    // pub(crate) fn remove_path_conditions_after(&mut self, block: BasicBlock) -> bool {
    //     self.mut_edge_conditions(|conditions| conditions.remove_after(block))
    // }
}
