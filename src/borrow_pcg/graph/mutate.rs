use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike},
        edge::kind::BorrowPcgEdgeKind,
        edge_data::{EdgeData, LabelEdgePlaces, LabelPlacePredicate},
        latest::Latest,
        path_condition::{PathCondition, PathConditions},
    },
    rustc_interface::{data_structures::fx::FxHashSet, middle::mir::BasicBlock},
    utils::{display::DisplayWithCompilerCtxt, CompilerCtxt, HasPlace, Place},
};

use super::BorrowsGraph;

impl<'tcx> BorrowsGraph<'tcx> {
    fn get_make_place_old_subgraph(
        &self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> BorrowsGraph<'tcx> {
        let mut place_roots = self
            .nodes(ctxt)
            .iter()
            .flat_map(|node| node.as_local_node(ctxt))
            .filter(|node| node.place() == place)
            .collect::<Vec<_>>();
        let mut subgraph = BorrowsGraph::new();
        let mut seen = FxHashSet::default();
        while let Some(root) = place_roots.pop() {
            if !seen.insert(root) {
                continue;
            }
            let blocking_edges = self.edges_blocking(root.into(), ctxt);
            for edge in blocking_edges {
                tracing::debug!("adding blocking edge: {}", edge.to_short_string(ctxt));
                subgraph.insert(edge.to_owned_edge(), ctxt);
                if let BorrowPcgEdgeKind::BorrowPcgExpansion(_) = edge.kind {
                    for node in edge.blocked_by_nodes(ctxt) {
                        tracing::debug!("adding root: {}", node.to_short_string(ctxt));
                        place_roots.push(node);
                    }
                }
            }

            let blocked_edges = self.edges_blocked_by(root, ctxt);
            for edge in blocked_edges {
                tracing::debug!("adding blocked-by edge: {}", edge.to_short_string(ctxt));
                subgraph.insert(edge.to_owned_edge(), ctxt);
                if let BorrowPcgEdgeKind::BorrowPcgExpansion(_) = edge.kind {
                    for node in edge.blocked_nodes(ctxt) {
                        if let Some(node) = node.as_local_node(ctxt) {
                            place_roots.push(node);
                        }
                    }
                }
            }
        }
        subgraph
    }
    pub(crate) fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let predicate = &LabelPlacePredicate::PrefixOrPostfix(place);
        let subgraph = self.get_make_place_old_subgraph(place, ctxt);
        if subgraph.num_edges() > 0 {
            subgraph.render_debug_graph(ctxt, "MPO subgraph");
        }
        tracing::debug!(
            "make {} old: {} edges",
            place.to_short_string(ctxt),
            subgraph.num_edges()
        );

        // First, label all edges in the subgraph as old in the current graph
        let mut changed = self.mut_edges(|edge| {
            let mut c = false;
            if subgraph.edges().any(|se| *se.kind == edge.kind) {
                tracing::debug!("labeling edge: {}", edge.to_short_string(ctxt));
                c |= edge.label_blocked_places(predicate, latest, ctxt);
                c |= edge.label_blocked_by_places(predicate, latest, ctxt);
            }
            c
        });

        // Then, re-insert the current versions of the expansion edges marked as
        // old, but should still be in the graph in their current version
        for edge in subgraph.edges() {
            if edge
                .blocked_by_nodes(ctxt)
                // .flat_map(|p| p.as_local_node(ctxt))
                .any(|p| p.place().is_prefix_exact(place))
            {
                changed |= self.insert(edge.to_owned_edge(), ctxt);
            }
        }
        tracing::debug!("make {} old: {}", place.to_short_string(ctxt), changed);
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

    fn mut_edge_conditions(&mut self, mut f: impl FnMut(&mut PathConditions) -> bool) -> bool {
        let mut changed = false;
        for (_, conditions) in self.edges.iter_mut() {
            if f(conditions) {
                changed = true;
            }
        }
        changed
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock], ctxt: CompilerCtxt<'_, 'tcx>) {
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
