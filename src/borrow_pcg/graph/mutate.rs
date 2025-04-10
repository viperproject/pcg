use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BorrowPCGEdge,
        has_pcs_elem::MakePlaceOld,
        latest::Latest,
        path_condition::{PathCondition, PathConditions},
    },
    rustc_interface::middle::mir::BasicBlock,
    utils::{Place, CompilerCtxt},
};

use super::BorrowsGraph;

impl<'tcx> BorrowsGraph<'tcx> {
    pub(in crate::borrow_pcg) fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.mut_edges(|edge| edge.make_place_old(place, latest, repacker))
    }

    pub(crate) fn mut_edges<'slf>(
        &'slf mut self,
        mut f: impl FnMut(&mut BorrowPCGEdge<'tcx>) -> bool,
    ) -> bool {
        let mut changed = false;
        self.edges = self
            .edges
            .drain()
            .map(|(kind, conditions)| {
                let mut edge = BorrowPCGEdge::new(kind, conditions);
                if f(&mut edge) {
                    changed = true;
                }
                (edge.kind, edge.conditions)
            })
            .collect();
        changed
    }

    fn mut_edge_conditions(&mut self, mut f: impl FnMut(&mut PathConditions) -> bool) -> bool {
        let mut changed = false;
        for (_, conditions) in self.edges.iter_mut() {
            if f(conditions) {
                changed = true;
            }
        }
        changed
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.edges
            .retain(|_, conditions| conditions.valid_for_path(path));
    }

    pub(crate) fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.mut_edge_conditions(|conditions| conditions.insert(pc))
    }
}
