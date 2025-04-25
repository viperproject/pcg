use crate::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use crate::borrow_pcg::coupling_graph_constructor::AbstractionGraphConstructor;
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::CompilerCtxt;
use crate::visualization::dot_graph::DotGraph;
use crate::visualization::generate_borrows_dot_graph;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::ToBorrowsEdge,
        edge::abstraction::{AbstractionBlockEdge, LoopAbstraction},
        latest::Latest,
        path_condition::PathConditions,
    },
    pcg::PCGNode,
    rustc_interface::middle::mir::{self, BasicBlock},
    utils::{
        display::DisplayDiff, maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace,
        validity::HasValidityCheck, PlaceSnapshot, SnapshotLocation,
    },
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
        if borrows_imgcat_debug() {
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self, location) {
                DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                    eprintln!("Error rendering self graph: {}", e);
                });
            }
        }
    }

    pub(crate) fn join<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> bool {
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
        if repacker.is_back_edge(other_block, self_block) {
            self.render_debug_graph(
                repacker,
                self_location,
                &format!("Self graph: {:?}", self_block),
            );
            other.render_debug_graph(
                repacker,
                other_location,
                &format!("Other graph: {:?}", other_block),
            );
            self.join_loop(other, self_block, other_block, repacker);
            let result = *self != old_self;
            if borrows_imgcat_debug() {
                if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self, self_location) {
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
            if let Ok(dot_graph) = generate_borrows_dot_graph(
                repacker,
                self,
                mir::Location {
                    block: self_block,
                    statement_index: 0,
                },
            ) {
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
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self, self_location) {
                DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {}", e);
                    },
                );
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, &old_self, self_location) {
                DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering old self graph: {}", e);
                });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, other, other_location) {
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
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) {
        let self_coupling_graph = AbstractionGraphConstructor::new(repacker, self_block)
            .construct_abstraction_graph(self, repacker.bc);
        let other_coupling_graph = AbstractionGraphConstructor::new(repacker, other_block)
            .construct_abstraction_graph(other, repacker.bc);

        if coupling_imgcat_debug() {
            self_coupling_graph
                .render_with_imgcat(repacker, &format!("self coupling graph: {:?}", self_block));
            other_coupling_graph.render_with_imgcat(
                repacker,
                &format!("other coupling graph: {:?}", other_block),
            );
        }

        let mut result = self_coupling_graph.clone();
        result.merge(&other_coupling_graph, repacker);
        if coupling_imgcat_debug() {
            result.render_with_imgcat(repacker, "merged coupling graph");
        }
        let to_keep = self.common_edges(other);
        self.edges
            .retain(|edge_kind, _| to_keep.contains(edge_kind));

        if borrows_imgcat_debug() {
            self.render_debug_graph(
                repacker,
                mir::Location {
                    block: self_block,
                    statement_index: 0,
                },
                "after removal of common edges",
            );
        }

        let other_coupling_edges = other_coupling_graph.edges().collect::<Vec<_>>();
        let self_coupling_edges = self_coupling_graph.edges().collect::<Vec<_>>();
        for tupl in result.edges() {
            if self_coupling_edges.iter().all(|other| other != &tupl)
                || other_coupling_edges.iter().all(|other| other != &tupl)
            {
                // This edge is missing from one of the graphs
                let (blocked, assigned, to_remove) = tupl;
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
                tracing::info!(
                    "Insert abstraction {}",
                    abstraction.to_short_string(repacker)
                );
                for edge in to_remove.iter() {
                    tracing::info!("To remove {}", edge.to_short_string(repacker));
                }

                self.insert(abstraction);
                self.edges
                    .retain(|edge_kind, _| !to_remove.contains(edge_kind));
            }
        }
        if borrows_imgcat_debug() {
            self.render_debug_graph(
                repacker,
                mir::Location {
                    block: self_block,
                    statement_index: 0,
                },
                "done",
            );
        }

        for coupled in result.roots() {
            for node in coupled {
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
}
