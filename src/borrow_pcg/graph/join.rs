use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeLike;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::graph::loop_abstraction::ConstructAbstractionGraphResult;
use crate::borrow_pcg::has_pcs_elem::{LabelLifetimeProjection, LabelLifetimeProjectionPredicate};
use crate::borrow_pcg::region_projection::LifetimeProjectionLabel;
use crate::free_pcs::OwnedPcg;
use crate::r#loop::PlaceUsages;
use crate::pcg::place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface};
use crate::pcg::{BodyAnalysis, PCGNodeLike, PcgError, PcgNode, PcgUnsupportedError};
use crate::pcg_validity_assert;
use crate::utils::data_structures::HashSet;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::{CompilerCtxt, Place, SnapshotLocation};
use crate::visualization::dot_graph::DotGraph;
use crate::visualization::generate_borrows_dot_graph;
use crate::{
    borrow_pcg::path_condition::ValidityConditions,
    rustc_interface::middle::{mir, mir::BasicBlock},
    utils::{display::DisplayDiff, validity::HasValidityCheck},
    validity_checks_enabled,
};

use super::{BorrowsGraph, borrows_imgcat_debug};

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn render_debug_graph(
        &self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
        comment: &str,
    ) {
        if borrows_imgcat_debug()
            && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, capabilities, self)
        {
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }

    fn apply_placeholder_labels<'mir>(
        &mut self,
        _capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) {
        let nodes = self.nodes(ctxt);
        for node in nodes {
            if let PcgNode::LifetimeProjection(rp) = node
                && rp.is_placeholder()
                && let Some(PcgNode::LifetimeProjection(local_rp)) = rp.try_to_local_node(ctxt)
            {
                // if let MaybeOldPlace::Current(place) = local_rp.base
                //     && capabilities.get(place).is_some()
                // {
                //     self.mut_edges(|edge| edge.label_region_projection(&local_rp, None, ctxt));
                // } else {
                let orig_rp = local_rp.with_label(None, ctxt);
                self.filter_mut_edges(|edge| {
                    edge.label_lifetime_projection(
                        &LabelLifetimeProjectionPredicate::Equals(orig_rp),
                        Some(LifetimeProjectionLabel::Placeholder),
                        ctxt,
                    )
                    .to_filter_mut_result()
                });
                // }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn join<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        body_analysis: &BodyAnalysis<'mir, 'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        owned: &mut OwnedPcg<'tcx>,
        path_conditions: ValidityConditions,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<bool, PcgError> {
        // For performance reasons we don't check validity here.
        // if validity_checks_enabled() {
        //     pcg_validity_assert!(other.is_valid(repacker), "Other graph is invalid");
        // }
        if ctxt.is_back_edge(other_block, self_block) {
            return Ok(false);
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
            )?;
            let result = *self != old_self;
            if borrows_imgcat_debug()
                && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, capabilities, self)
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
            // self.apply_placeholder_labels(capabilities, ctxt);
            return Ok(result);
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

        // if borrows_imgcat_debug()
        //     && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self)
        // {
        //     DotGraph::render_with_imgcat(&dot_graph, &format!("After join: (changed={changed:?})"))
        //         .unwrap_or_else(|e| {
        //             eprintln!("Error rendering self graph: {e}");
        //         });
        //     if changed {
        //         eprintln!("{}", old_self.fmt_diff(self, ctxt))
        //     }
        // }

        // For performance reasons we only check validity here if we are also producing debug graphs
        if validity_checks_enabled() && borrows_imgcat_debug() && !self.is_valid(ctxt) {
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, capabilities, self) {
                DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {e}");
                    },
                );
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, capabilities, &old_self) {
                DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering old self graph: {e}");
                });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, capabilities, other) {
                DotGraph::render_with_imgcat(&dot_graph, "Other graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering other graph: {e}");
                });
            }
            pcg_validity_assert!(
                false,
                "Graph became invalid after join. self: {self_block:?}, other: {other_block:?}"
            );
        }
        Ok(changed)
    }

    #[allow(clippy::too_many_arguments)]
    fn join_loop<'mir>(
        &mut self,
        loop_head: BasicBlock,
        used_places: &PlaceUsages<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        owned: &mut OwnedPcg<'tcx>,
        path_conditions: ValidityConditions,
        body_analysis: &BodyAnalysis<'mir, 'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError> {
        tracing::debug!("used places: {}", used_places.to_short_string(ctxt));
        // p_loop
        let live_loop_places = used_places.usages_where(|p| {
            body_analysis.is_live_and_initialized_at(
                mir::Location {
                    block: loop_head,
                    statement_index: 0,
                },
                p.place,
            )
        });

        if !live_loop_places
            .usages_where(|p| p.place.contains_unsafe_deref(ctxt))
            .is_empty()
        {
            return Err(PcgUnsupportedError::DerefUnsafePtr.into());
        }

        tracing::debug!(
            "live loop places: {}",
            live_loop_places.to_short_string(ctxt)
        );

        let loop_blocked_places = live_loop_places.usages_where(|p| {
            ctxt.bc.is_directly_blocked(
                p.place,
                mir::Location {
                    block: loop_head,
                    statement_index: 0,
                },
                ctxt,
            )
        });

        tracing::debug!(
            "loop_blocked_places: {}",
            loop_blocked_places.to_short_string(ctxt)
        );

        let loop_blocker_places =
            live_loop_places.usages_where(|p| !p.place.regions(ctxt).is_empty());

        tracing::debug!(
            "loop_blocker_places: {}",
            loop_blocker_places.to_short_string(ctxt)
        );

        let expand_places = loop_blocker_places.joined_with(&loop_blocked_places);

        self.expand_places_for_abstraction(
            loop_head,
            &loop_blocked_places,
            &expand_places,
            capabilities,
            owned,
            path_conditions.clone(),
            ctxt,
        );
        self.render_debug_graph(capabilities, ctxt, "G_Pre'");

        // p_roots
        let live_roots = live_loop_places
            .iter()
            .flat_map(|p| self.get_borrow_roots(p.place, loop_head, ctxt))
            .collect::<HashSet<_>>();

        tracing::debug!("live roots: {}", live_roots.to_short_string(ctxt));

        let root_places = live_roots
            .iter()
            .flat_map(|node| node.related_maybe_remote_current_place())
            .filter(|p| {
                !(p.is_local() && live_loop_places.contains(p.relevant_place_for_blocking()))
            })
            .collect::<HashSet<_>>();

        tracing::debug!("root places: {}", root_places.to_short_string(ctxt));

        let ConstructAbstractionGraphResult {
            graph: abstraction_graph,
            to_label,
            capability_updates,
        } = self.get_loop_abstraction_graph(
            &loop_blocked_places,
            root_places,
            &loop_blocker_places,
            loop_head,
            path_conditions.clone(),
            ctxt,
        );

        abstraction_graph.render_debug_graph(capabilities, ctxt, "Abstraction graph");

        for rp in to_label.iter() {
            self.filter_mut_edges(|edge| {
                edge.label_lifetime_projection(
                    rp,
                    Some(LifetimeProjectionLabel::Location(SnapshotLocation::Loop(
                        loop_head,
                    ))),
                    ctxt,
                )
                .to_filter_mut_result()
            });
        }

        for (place, cap_option) in capability_updates {
            if let Some(cap) = cap_option {
                capabilities.insert(place, cap, ctxt);
            } else {
                capabilities.remove(place, ctxt);
            }
        }

        let abstraction_graph_pcg_nodes = abstraction_graph.nodes(ctxt);
        let to_cut = self.identify_subgraph_to_cut(abstraction_graph_pcg_nodes, ctxt);
        to_cut.render_debug_graph(capabilities, ctxt, "To cut");
        self.render_debug_graph(capabilities, ctxt, "Self before cut");
        for edge in to_cut.edges() {
            self.remove(edge.kind());
        }
        self.render_debug_graph(capabilities, ctxt, "Self after cut");
        for edge in abstraction_graph.into_edges() {
            self.insert(edge, ctxt);
        }
        let self_places = self.places(ctxt);
        for place in to_cut.places(ctxt) {
            if !place.is_owned(ctxt)
                && capabilities.get(place, ctxt).is_some()
                && !self_places.contains(&place)
            {
                capabilities.remove(place, ctxt);
            }
        }
        self.render_debug_graph(capabilities, ctxt, "Final graph");
        Ok(())
    }
}
