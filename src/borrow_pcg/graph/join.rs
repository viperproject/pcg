use crate::borrow_pcg::abstraction_graph_constructor::AbstractionGraphConstructor;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::pcg_validity_assert;
use crate::utils::CompilerCtxt;
use crate::visualization::dot_graph::DotGraph;
use crate::visualization::generate_borrows_dot_graph;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::ToBorrowsEdge,
        edge::abstraction::{AbstractionBlockEdge, LoopAbstraction},
        path_condition::PathConditions,
    },
    rustc_interface::middle::mir::{self, BasicBlock},
    utils::{display::DisplayDiff, validity::HasValidityCheck},
    validity_checks_enabled,
};

use super::{borrows_imgcat_debug, coupling_imgcat_debug, BorrowsGraph};

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn render_debug_graph(
        &self,
        repacker: CompilerCtxt<'_, 'tcx>,
        location: mir::Location,
        comment: &str,
    ) {
        if borrows_imgcat_debug()
            && let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self, location)
        {
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }

    pub(crate) fn join<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> bool {
        tracing::info!("join {self_block:?} {other_block:?} start");
        // For performance reasons we don't check validity here.
        // if validity_checks_enabled() {
        //     pcg_validity_assert!(other.is_valid(repacker), "Other graph is invalid");
        // }
        let old_self = self.clone();

        let self_location = mir::Location {
            block: self_block,
            statement_index: 0,
        };
        let other_location = mir::Location {
            block: other_block,
            statement_index: 0,
        };
        if ctxt.is_back_edge(other_block, self_block) {
            self.render_debug_graph(ctxt, self_location, &format!("Self graph: {self_block:?}"));
            other.render_debug_graph(
                ctxt,
                other_location,
                &format!("Other graph: {other_block:?}"),
            );
            self.join_loop(other, self_block, other_block, ctxt);
            let result = *self != old_self;
            if borrows_imgcat_debug()
                && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self, self_location)
            {
                DotGraph::render_with_imgcat(
                    &dot_graph,
                    &format!("After join (loop, changed={result:?}):"),
                )
                .unwrap_or_else(|e| {
                    eprintln!("Error rendering self graph: {e}");
                });
                if result {
                    eprintln!("{}", old_self.fmt_diff(self, ctxt))
                }
            }
            // For performance reasons we don't check validity here.
            // if validity_checks_enabled() {
            //     assert!(self.is_valid(repacker), "Graph became invalid after join");
            // }
            return result;
        }
        for other_edge in other.edges() {
            self.insert(other_edge.to_owned_edge());
        }
        for edge in self
            .edges()
            .map(|edge| edge.to_owned_edge())
            .collect::<Vec<_>>()
        {
            if let BorrowPcgEdgeKind::Abstraction(_) = edge.kind() {
                continue;
            }
            if self.is_encapsulated_by_abstraction(&edge, ctxt) {
                self.remove(&edge);
            }
        }

        let changed = old_self != *self;

        if borrows_imgcat_debug()
            && let Ok(dot_graph) = generate_borrows_dot_graph(
                ctxt,
                self,
                mir::Location {
                    block: self_block,
                    statement_index: 0,
                },
            )
        {
            DotGraph::render_with_imgcat(&dot_graph, &format!("After join: (changed={changed:?})"))
                .unwrap_or_else(|e| {
                    eprintln!("Error rendering self graph: {e}");
                });
            if changed {
                eprintln!("{}", old_self.fmt_diff(self, ctxt))
            }
        }

        // For performance reasons we only check validity here if we are also producing debug graphs
        if validity_checks_enabled() && borrows_imgcat_debug() && !self.is_valid(ctxt) {
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self, self_location) {
                DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {e}");
                    },
                );
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, &old_self, self_location) {
                DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering old self graph: {e}");
                });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, other, other_location) {
                DotGraph::render_with_imgcat(&dot_graph, "Other graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering other graph: {e}");
                });
            }
            panic!("Graph became invalid after join. self: {self_block:?}, other: {other_block:?}");
        }
        changed
    }

    fn join_loop<'mir>(
        &mut self,
        other: &Self,
        loop_head: BasicBlock,
        from_block: BasicBlock,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) {
        assert!(from_block > loop_head);
        tracing::info!("join_loop {from_block:?} {loop_head:?} start");
        let self_abstraction_graph = AbstractionGraphConstructor::new(ctxt, from_block)
            .construct_abstraction_graph(self, ctxt.bc);
        let other_coupling_graph = AbstractionGraphConstructor::new(ctxt, loop_head)
            .construct_abstraction_graph(other, ctxt.bc);

        if coupling_imgcat_debug() {
            self_abstraction_graph
                .render_with_imgcat(ctxt, &format!("self coupling graph: {from_block:?}"));
            other_coupling_graph
                .render_with_imgcat(ctxt, &format!("other coupling graph: {loop_head:?}"));
        }

        let to_keep = self.common_edges(other);
        self.edges
            .retain(|edge_kind, _| to_keep.contains(edge_kind));

        if borrows_imgcat_debug() {
            self.render_debug_graph(
                ctxt,
                mir::Location {
                    block: from_block,
                    statement_index: 0,
                },
                "after removal of common edges",
            );
        }

        let mut result = self_abstraction_graph.clone();
        result.merge(&other_coupling_graph, ctxt);
        if coupling_imgcat_debug() {
            result.render_with_imgcat(ctxt, "merged coupling graph");
        }
        let other_coupling_edges = other_coupling_graph.edges().collect::<Vec<_>>();
        let self_coupling_edges = self_abstraction_graph.edges().collect::<Vec<_>>();
        for tupl in result.edges() {
            if self_coupling_edges.iter().all(|other| other != &tupl)
                || other_coupling_edges.iter().all(|other| other != &tupl)
            {
                // This edge is missing from one of the graphs
                let (blocked, assigned, to_remove) = tupl;
                let abstraction = LoopAbstraction::new(
                    AbstractionBlockEdge::new(
                        blocked.clone().into_iter().map(|node| *node).collect(),
                        assigned
                            .clone()
                            .into_iter()
                            .map(|node| {
                                node.try_into().unwrap_or_else(|_e| {
                                    panic!("Failed to convert node {node:?} to node index");
                                })
                            })
                            .collect(),
                    ),
                    loop_head,
                )
                .to_borrow_pcg_edge(PathConditions::new(loop_head));

                self.insert(abstraction);
                self.edges
                    .retain(|edge_kind, _| !to_remove.contains(edge_kind));
            }
        }
        if validity_checks_enabled() {
            for edge in self.edges() {
                pcg_validity_assert!(edge.conditions().all_not_after(loop_head));
            }
        }
        if borrows_imgcat_debug() {
            self.render_debug_graph(
                ctxt,
                mir::Location {
                    block: from_block,
                    statement_index: 0,
                },
                "done",
            );
        }
        tracing::info!("join_loop {from_block:?} {loop_head:?} end");
    }
}
