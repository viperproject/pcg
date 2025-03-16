use crate::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::visualization::dot_graph::DotGraph;
use crate::visualization::generate_borrows_dot_graph;
use crate::{borrow_pcg::coupling_graph_constructor::BorrowCheckerInterface, utils::PlaceRepacker};
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::ToBorrowsEdge,
        edge::abstraction::{AbstractionBlockEdge, LoopAbstraction},
        latest::Latest,
        path_condition::PathConditions,
    },
    combined_pcs::PCGNode,
    rustc_interface::
        middle::mir::BasicBlock
    ,
    utils::{
        display::DisplayDiff,
        maybe_old::MaybeOldPlace,
        maybe_remote::MaybeRemotePlace,
        validity::HasValidityCheck,
        PlaceSnapshot, SnapshotLocation,
    },
    validity_checks_enabled,
};

use super::{borrows_imgcat_debug, coupling_imgcat_debug, BorrowsGraph};

impl<'tcx> BorrowsGraph<'tcx> {

    pub(crate) fn join<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        repacker: PlaceRepacker<'mir, 'tcx>,
        bc: &dyn BorrowCheckerInterface<'mir, 'tcx>,
    ) -> bool {
        // For performance reasons we don't check validity here.
        // if validity_checks_enabled() {
        //     pcg_validity_assert!(other.is_valid(repacker), "Other graph is invalid");
        // }
        #[allow(unused)]
        let old_self = self.clone();

        #[allow(unused)]
        let other_frozen = other.frozen_graph();

        if borrows_imgcat_debug() {
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                DotGraph::render_with_imgcat(&dot_graph, &format!("Self graph: {:?}", self_block))
                    .unwrap_or_else(|e| {
                        eprintln!("Error rendering self graph: {}", e);
                    });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, other) {
                DotGraph::render_with_imgcat(
                    &dot_graph,
                    &format!("Other graph: {:?}", other_block),
                )
                .unwrap_or_else(|e| {
                    eprintln!("Error rendering other graph: {}", e);
                });
            }
        }

        if repacker.is_back_edge(other_block, self_block) {
            self.join_loop(other, self_block, other_block, repacker, bc);
            let result = *self != old_self;
            if borrows_imgcat_debug() {
                if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                    DotGraph::render_with_imgcat(
                        &dot_graph,
                        &format!("After join (loop, changed={:?}):", result),
                    )
                    .unwrap_or_else(|e| {
                        eprintln!("Error rendering self graph: {}", e);
                    });
                    if result {
                        eprintln!("{}", old_self.fmt_diff(self, repacker))
                    }
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
            if let BorrowPCGEdgeKind::Abstraction(_) = edge.kind() {
                continue;
            }
            if self.is_encapsulated_by_abstraction(&edge, repacker) {
                self.remove(&edge);
            }
        }

        let changed = old_self != *self;

        if borrows_imgcat_debug() {
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                DotGraph::render_with_imgcat(
                    &dot_graph,
                    &format!("After join: (changed={:?})", changed),
                )
                .unwrap_or_else(|e| {
                    eprintln!("Error rendering self graph: {}", e);
                });
                if changed {
                    eprintln!("{}", old_self.fmt_diff(self, repacker))
                }
            }
        }

        // For performance reasons we only check validity here if we are also producing debug graphs
        if validity_checks_enabled() && borrows_imgcat_debug() && !self.is_valid(repacker) {
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {}", e);
                    },
                );
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, &old_self) {
                DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering old self graph: {}", e);
                });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, other) {
                DotGraph::render_with_imgcat(&dot_graph, "Other graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering other graph: {}", e);
                });
            }
            panic!(
                "Graph became invalid after join. self: {:?}, other: {:?}",
                self_block, other_block
            );
        }
        changed
    }

    fn join_loop<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        repacker: PlaceRepacker<'mir, 'tcx>,
        borrow_checker: &dyn BorrowCheckerInterface<'mir, 'tcx>,
    ) {
        let common_edges = self.common_edges(other);
        let mut without_common_self = self.clone();
        let mut without_common_other = other.clone();
        for edge in common_edges.iter() {
            tracing::debug!("Removing common edge: {:?}", edge);
            without_common_self.edges.remove(edge);
            without_common_other.edges.remove(edge);
        }

        let self_coupling_graph = without_common_self.construct_region_projection_abstraction(
            borrow_checker,
            repacker,
            other_block,
        );

        let other_coupling_graph = without_common_other.construct_region_projection_abstraction(
            borrow_checker,
            repacker,
            other_block,
        );

        if coupling_imgcat_debug() {
            self_coupling_graph
                .render_with_imgcat(repacker, &format!("self coupling graph: {:?}", self_block));
            other_coupling_graph.render_with_imgcat(
                repacker,
                &format!("other coupling graph: {:?}", other_block),
            );
        }

        let mut result = self_coupling_graph;
        result.merge(&other_coupling_graph, repacker);
        if coupling_imgcat_debug() {
            result.render_with_imgcat(repacker, "merged coupling graph");
        }

        self.edges
            .retain(|edge_kind, _| common_edges.contains(edge_kind));

        for (blocked, assigned) in result.edges() {
            let abstraction = LoopAbstraction::new(
                AbstractionBlockEdge::new(
                    blocked.clone().into_iter().collect(),
                    assigned
                        .clone()
                        .into_iter()
                        .map(|node| node.try_into().unwrap())
                        .collect(),
                ),
                self_block,
            )
            .to_borrow_pcg_edge(PathConditions::new(self_block));

            self.insert(abstraction);
        }
        for node in result.roots() {
            if let PCGNode::RegionProjection(rp) = node {
                if let MaybeRemotePlace::Local(MaybeOldPlace::Current { place }) = rp.place() {
                    let mut old_rp = rp;
                    old_rp.base =
                        PlaceSnapshot::new(place, SnapshotLocation::Start(self_block)).into();
                    let latest = Latest::singleton(place, SnapshotLocation::Start(self_block));
                    self.make_place_old(place, &latest, repacker);
                }
            }
        }
    }
}
