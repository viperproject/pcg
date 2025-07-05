use crate::borrow_pcg::abstraction_graph_constructor::AbstractionGraphConstructor;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion};
use crate::borrow_pcg::domain::LoopAbstractionInput;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::has_pcs_elem::LabelRegionProjection;
use crate::borrow_pcg::region_projection::RegionProjectionLabel;
use crate::coupling::coupled::Coupled;
use crate::pcg::place_capabilities::PlaceCapabilities;
use crate::pcg::{PCGNode, PCGNodeLike};
use crate::r#loop::LoopPlaceUsageAnalysis;
use crate::utils::data_structures::HashSet;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::loop_usage::LoopUsage;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::{CompilerCtxt, Place, SnapshotLocation};
use crate::visualization::dot_graph::DotGraph;
use crate::visualization::generate_borrows_dot_graph;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::ToBorrowsEdge,
        edge::abstraction::{r#loop::LoopAbstraction, AbstractionBlockEdge},
        path_condition::PathConditions,
    },
    rustc_interface::middle::{mir, mir::BasicBlock},
    utils::{display::DisplayDiff, validity::HasValidityCheck},
    validity_checks_enabled,
};

use super::{borrows_imgcat_debug, coupling_imgcat_debug, BorrowsGraph};

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn render_debug_graph(&self, ctxt: CompilerCtxt<'_, 'tcx>, comment: &str) {
        if borrows_imgcat_debug()
            && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self)
        {
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }

    fn apply_placeholder_labels<'mir>(
        &mut self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) {
        let nodes = self.nodes(ctxt);
        for node in nodes {
            if let PCGNode::RegionProjection(rp) = node
                && rp.is_placeholder()
                && let Some(PCGNode::RegionProjection(local_rp)) = rp.try_to_local_node(ctxt)
            {
                if let MaybeOldPlace::Current { place } = local_rp.base
                    && capabilities.get(place).is_some()
                {
                    self.mut_edges(|edge| edge.label_region_projection(&local_rp, None, ctxt));
                } else {
                    let orig_rp = local_rp.with_label(None, ctxt);
                    self.mut_edges(|edge| {
                        edge.label_region_projection(
                            &orig_rp,
                            Some(RegionProjectionLabel::Placeholder),
                            ctxt,
                        )
                    });
                }
            }
        }
    }

    pub(crate) fn join<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        loop_usage: &LoopPlaceUsageAnalysis<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> bool {
        tracing::info!("join {self_block:?} {other_block:?} start");
        // For performance reasons we don't check validity here.
        // if validity_checks_enabled() {
        //     pcg_validity_assert!(other.is_valid(repacker), "Other graph is invalid");
        // }
        if ctxt.is_back_edge(other_block, self_block) {
            return false;
        }
        let old_self = self.clone();

        if let Some(used_places) = loop_usage.get_used_places(self_block) {
            // self.render_debug_graph(ctxt, &format!("Self graph: {self_block:?}"));
            // other.render_debug_graph(ctxt, &format!("Other graph: {other_block:?}"));
            self.join_loop(other, self_block, other_block, used_places, ctxt);
            let result = *self != old_self;
            if borrows_imgcat_debug()
                && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self)
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
            self.apply_placeholder_labels(capabilities, ctxt);
            return result;
        }
        for other_edge in other.edges() {
            self.insert(other_edge.to_owned_edge(), ctxt);
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
                self.remove(edge.kind());
            }
        }

        self.apply_placeholder_labels(capabilities, ctxt);

        let changed = old_self != *self;

        if borrows_imgcat_debug()
            && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self)
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
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self) {
                DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {e}");
                    },
                );
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, &old_self) {
                DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering old self graph: {e}");
                });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, other) {
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
        pre_block_state: &Self,
        loop_head: BasicBlock,
        pre_block: BasicBlock,
        used_places: &HashSet<Place<'tcx>>, // L
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) {
        tracing::info!("join_loop with places {:?}", used_places);
        // E_Pre
        let loop_places_subgraph = pre_block_state.get_subgraph_for_places(used_places, ctxt);
        loop_places_subgraph
            .render_debug_graph(ctxt, &format!("loop_places_subgraph: {loop_head:?}"));

        let mut base_abstracted_subgraph =
            loop_places_subgraph.base_abstraction_graph(loop_head, ctxt);

        let mut maybe_borrowed_places = used_places.clone();
        for root in loop_places_subgraph.roots(ctxt) {
            if let PCGNode::Place(p) = root
                && let Some(current_place) = p.as_current_place()
            {
                maybe_borrowed_places.insert(current_place);
            }
        }
        let nodes_to_block_check = loop_places_subgraph
            .nodes(ctxt)
            .into_iter()
            .filter(|n| {
                if let Some(p) = n.related_current_place() {
                    !p.projects_shared_ref(ctxt)
                } else {
                    false
                }
            })
            .collect::<Vec<_>>();
        base_abstracted_subgraph.render_with_imgcat(ctxt, "base_abstracted_subgraph (before)");
        for n1 in nodes_to_block_check.iter() {
            for n2 in nodes_to_block_check.iter() {
                if n1 == n2 {
                    continue;
                }
                if ctxt.bc().blocks(
                    n1.related_current_place().unwrap(),
                    n2.related_current_place().unwrap(),
                    mir::Location {
                        block: loop_head,
                        statement_index: 0,
                    },
                    ctxt,
                ) {
                    tracing::info!(
                        "{} blocks {}",
                        n1.to_short_string(ctxt),
                        n2.to_short_string(ctxt)
                    );
                    base_abstracted_subgraph.add_edge(
                        &Coupled::singleton(n2.as_abstraction_graph_node(loop_head, ctxt).unwrap()),
                        &Coupled::singleton(n1.as_abstraction_graph_node(loop_head, ctxt).unwrap()),
                        HashSet::default(),
                        ctxt,
                    );
                }
            }
        }
        // base_abstracted_subgraph.render_with_imgcat(ctxt, "base_abstracted_subgraph");
        let abstracted_subgraph = AbstractionGraphConstructor::new(ctxt, loop_head)
            .remove_intermediate_nodes(pre_block_state, base_abstracted_subgraph, ctxt.bc);
        if borrows_imgcat_debug() {
            abstracted_subgraph.render_with_imgcat(ctxt, "abstracted_subgraph");
        }

        *self = pre_block_state.diff(&loop_places_subgraph, ctxt);

        for (blocked, assigned, to_remove) in abstracted_subgraph.edges() {
            let abstraction = LoopAbstraction::new(
                AbstractionBlockEdge::new(
                    blocked.clone().into_iter().map(|node| node.to_pcg_node(ctxt).into()).collect(),
                    assigned
                        .clone()
                        .into_iter()
                        .map(|node| node.0.try_to_local_node(ctxt).unwrap().into())
                        .collect(),
                    ctxt,
                ),
                loop_head,
            )
            .to_borrow_pcg_edge(PathConditions::new());

            self.insert(abstraction, ctxt);
        }

        // if borrows_imgcat_debug() {
        //     self.render_debug_graph(ctxt, "done");
        // }
        tracing::debug!("join_loop {pre_block:?} {loop_head:?} end");
    }
}
