use crate::borrow_pcg::abstraction_graph_constructor::AbstractionGraphConstructor;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion};
use crate::borrow_pcg::domain::{AbstractionOutputTarget, LoopAbstractionInput};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::graph::loop_abstraction::ConstructAbstractionGraphResult;
use crate::borrow_pcg::has_pcs_elem::{LabelRegionProjection, LabelRegionProjectionPredicate};
use crate::borrow_pcg::region_projection::RegionProjectionLabel;
use crate::coupling::coupled::Coupled;
use crate::free_pcs::FreePlaceCapabilitySummary;
use crate::pcg::place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface};
use crate::pcg::{BodyAnalysis, PCGNode, PCGNodeLike};
use crate::r#loop::LoopPlaceUsageAnalysis;
use crate::utils::data_structures::HashSet;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::liveness::PlaceLiveness;
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
                    self.mut_edges(|edge| {
                        edge.label_region_projection(
                            &LabelRegionProjectionPredicate::Equals(local_rp),
                            None,
                            ctxt,
                        )
                    });
                } else {
                    let orig_rp = local_rp.with_label(None, ctxt);
                    self.mut_edges(|edge| {
                        edge.label_region_projection(
                            &LabelRegionProjectionPredicate::Equals(orig_rp),
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
        body_analysis: &BodyAnalysis<'mir, 'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        owned: &mut FreePlaceCapabilitySummary<'tcx>,
        path_conditions: PathConditions,
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

        if let Some(used_places) = body_analysis.get_places_used_in_loop(self_block) {
            // self.render_debug_graph(ctxt, &format!("Self graph: {self_block:?}"));
            // other.render_debug_graph(ctxt, &format!("Other graph: {other_block:?}"));

            self.join_loop(
                self_block,
                used_places,
                capabilities,
                owned,
                path_conditions,
                body_analysis,
                ctxt,
            );
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
        loop_head: BasicBlock,
        used_places: &HashSet<Place<'tcx>>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        owned: &mut FreePlaceCapabilitySummary<'tcx>,
        path_conditions: PathConditions,
        body_analysis: &BodyAnalysis<'mir, 'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) {
        tracing::info!("used_places: {}", used_places.to_short_string(ctxt));
        let loop_places = used_places
            .iter()
            .copied()
            .filter(|p| {
                body_analysis.is_live_and_initialized_at(
                    mir::Location {
                        block: loop_head,
                        statement_index: 0,
                    },
                    *p,
                )
            })
            .collect::<HashSet<_>>();

        tracing::info!("live loop places: {}", loop_places.to_short_string(ctxt));

        // n_loop
        let live_loop_nodes = loop_places
            .iter()
            .flat_map(|p| {
                let mut nodes = p
                    .region_projections(ctxt)
                    .into_iter()
                    .map(|rp| rp.into())
                    .collect::<Vec<_>>();
                if !p.is_owned(ctxt) {
                    nodes.push((*p).into())
                }
                nodes
            })
            .collect::<HashSet<_>>();

        tracing::info!("live loop_nodes: {}", live_loop_nodes.to_short_string(ctxt));

        self.unpack_places_for_abstraction(
            loop_head,
            &loop_places,
            capabilities,
            owned,
            path_conditions.clone(),
            ctxt,
        );
        self.render_debug_graph(ctxt, "G_Pre'");

        // n_roots
        let live_roots = live_loop_nodes
            .iter()
            .flat_map(|p| {
                self.get_immediate_live_ancestors(
                    *p,
                    &body_analysis.place_liveness,
                    mir::Location {
                        block: loop_head,
                        statement_index: 0,
                    },
                    ctxt,
                )
            })
            .collect::<HashSet<_>>();

        tracing::info!("live roots: {}", live_roots.to_short_string(ctxt));

        let ConstructAbstractionGraphResult {
            graph: abstraction_graph,
            to_label,
            to_remove,
        } = self.get_loop_abstraction_graph(
            live_loop_nodes,
            live_roots,
            loop_head,
            path_conditions.clone(),
            ctxt,
        );

        abstraction_graph.render_debug_graph(ctxt, "Abstraction graph");

        for rp in to_label.iter() {
            self.mut_edges(|edge| {
                edge.label_region_projection(
                    rp,
                    Some(RegionProjectionLabel::Location(SnapshotLocation::Start(
                        loop_head,
                    ))),
                    ctxt,
                )
            });
        }

        for place in to_remove {
            capabilities.remove(place);
        }

        let abstraction_graph_pcg_nodes = abstraction_graph.nodes(ctxt);
        let to_cut = self.identify_subgraph_to_cut(abstraction_graph_pcg_nodes, ctxt);
        to_cut.render_debug_graph(ctxt, "To cut");
        self.render_debug_graph(ctxt, "Self before cut");
        for edge in to_cut.edges() {
            self.remove(&edge.kind());
        }
        self.render_debug_graph(ctxt, "Self after cut");
        for edge in abstraction_graph.into_edges() {
            self.insert(edge, ctxt);
        }
    }
}
