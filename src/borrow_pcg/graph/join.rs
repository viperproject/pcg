use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeLike;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::graph::loop_abstraction::ConstructAbstractionGraphResult;
use crate::borrow_pcg::has_pcs_elem::{LabelLifetimeProjection, LabelLifetimeProjectionPredicate};
use crate::borrow_pcg::region_projection::LifetimeProjectionLabel;
use crate::error::{PcgError, PcgUnsupportedError};
use crate::r#loop::PlaceUsages;
use crate::owned_pcg::OwnedPcg;
use crate::pcg::ctxt::AnalysisCtxt;
use crate::pcg::place_capabilities::{
    PlaceCapabilitiesInterface, PlaceCapabilitiesReader, SymbolicPlaceCapabilities,
};
use crate::pcg::{BodyAnalysis, PCGNodeLike, PcgNode, SymbolicCapability};
use crate::pcg_validity_assert;
use crate::utils::data_structures::HashSet;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::logging::LogPredicate;
use crate::utils::{CompilerCtxt, DebugImgcat, HasBorrowCheckerCtxt, SnapshotLocation, logging};
use crate::visualization::dot_graph::DotGraph;
use crate::visualization::generate_borrows_dot_graph;
use crate::{
    borrow_pcg::path_condition::ValidityConditions,
    rustc_interface::middle::{mir, mir::BasicBlock},
    utils::validity::HasValidityCheck,
    validity_checks_enabled,
};

use super::{BorrowsGraph, borrows_imgcat_debug};

pub(crate) struct JoinBorrowsArgs<'pcg, 'a, 'tcx> {
    pub(crate) self_block: BasicBlock,
    pub(crate) other_block: BasicBlock,
    pub(crate) body_analysis: &'pcg BodyAnalysis<'a, 'tcx>,
    pub(crate) capabilities: &'pcg mut SymbolicPlaceCapabilities<'tcx>,
    pub(crate) owned: &'pcg mut OwnedPcg<'tcx>,
}

impl<'mir, 'tcx> JoinBorrowsArgs<'_, 'mir, 'tcx> {
    pub(crate) fn reborrow<'slf>(&'slf mut self) -> JoinBorrowsArgs<'slf, 'mir, 'tcx> {
        JoinBorrowsArgs {
            self_block: self.self_block,
            other_block: self.other_block,
            body_analysis: self.body_analysis,
            capabilities: self.capabilities,
            owned: self.owned,
        }
    }
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn render_debug_graph<'a>(
        &self,
        block: mir::BasicBlock,
        debug_imgcat: Option<DebugImgcat>,
        capabilities: &impl PlaceCapabilitiesReader<'tcx>,
        comment: &str,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
        if borrows_imgcat_debug(block, debug_imgcat)
            && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, capabilities, self)
        {
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }

    fn apply_placeholder_labels<'mir>(
        &mut self,
        _capabilities: &impl PlaceCapabilitiesReader<'tcx, SymbolicCapability>,
        ctxt: impl HasBorrowCheckerCtxt<'mir, 'tcx>,
    ) where
        'tcx: 'mir,
    {
        let nodes = self.nodes(ctxt);
        for node in nodes {
            if let PcgNode::LifetimeProjection(rp) = node
                && rp.is_future()
                && let Some(PcgNode::LifetimeProjection(local_rp)) = rp.try_to_local_node(ctxt)
            {
                let orig_rp = local_rp.with_label(None, ctxt);
                self.filter_mut_edges(|edge| {
                    edge.label_lifetime_projection(
                        &LabelLifetimeProjectionPredicate::Equals(orig_rp),
                        Some(LifetimeProjectionLabel::Future),
                        ctxt.bc_ctxt(),
                    )
                    .to_filter_mut_result()
                });
            }
        }
    }

    pub(crate) fn join<'slf, 'a>(
        &'slf mut self,
        other_graph: &'slf BorrowsGraph<'tcx>,
        validity_conditions: &'slf ValidityConditions,
        mut args: JoinBorrowsArgs<'slf, 'a, 'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        let other_block = args.other_block;
        let self_block = args.self_block;
        pcg_validity_assert!(other_graph.is_valid(ctxt), [ctxt], "Other graph is invalid");
        pcg_validity_assert!(
            !ctxt.ctxt.is_back_edge(other_block, self_block),
            [ctxt],
            "Joining back edge from {other_block:?} to {self_block:?}"
        );
        let old_self = self.clone();

        if let Some(used_places) = args.body_analysis.get_places_used_in_loop(self_block) {
            self.join_loop(used_places, validity_conditions, args.reborrow(), ctxt)?;
            if borrows_imgcat_debug(self_block, Some(DebugImgcat::JoinLoop))
                && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, args.capabilities, self)
            {
                DotGraph::render_with_imgcat(&dot_graph, "After join (loop):").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {e}");
                    },
                );
            }
            pcg_validity_assert!(
                self.is_valid(ctxt),
                [ctxt],
                "Graph became invalid after join"
            );
            return Ok(());
        }
        for other_edge in other_graph.edges() {
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

        self.apply_placeholder_labels(args.capabilities, ctxt);

        if validity_checks_enabled() && !self.is_valid(ctxt) {
            pcg_validity_assert!(
                false,
                [ctxt],
                "Graph became invalid after join. self: {self_block:?}, other: {other_block:?}"
            );
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, args.capabilities, self) {
                DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {e}");
                    },
                );
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, args.capabilities, &old_self) {
                DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering old self graph: {e}");
                });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, args.capabilities, other_graph)
            {
                DotGraph::render_with_imgcat(&dot_graph, "Other graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering other graph: {e}");
                });
            }
        }
        Ok(())
    }

    fn join_loop<'mir>(
        &mut self,
        used_places: &PlaceUsages<'tcx>,
        validity_conditions: &ValidityConditions,
        mut args: JoinBorrowsArgs<'_, 'mir, 'tcx>,
        ctxt: AnalysisCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError> {
        let loop_head = args.self_block;
        logging::log!(
            LogPredicate::DebugBlock,
            ctxt,
            "used places: {}",
            used_places.to_short_string(ctxt.ctxt)
        );
        // p_loop
        let live_loop_places = used_places.usages_where(|p| {
            args.body_analysis.is_live_and_initialized_at(
                mir::Location {
                    block: args.self_block,
                    statement_index: 0,
                },
                p.place,
            )
        });

        if !live_loop_places
            .usages_where(|p| p.place.contains_unsafe_deref(ctxt.ctxt))
            .is_empty()
        {
            return Err(PcgUnsupportedError::DerefUnsafePtr.into());
        }

        logging::log!(
            LogPredicate::DebugBlock,
            ctxt,
            "live loop places: {}",
            live_loop_places.to_short_string(ctxt.ctxt)
        );

        let loop_blocked_places = live_loop_places.usages_where(|p| {
            ctxt.ctxt.bc.is_directly_blocked(
                p.place,
                mir::Location {
                    block: args.self_block,
                    statement_index: 0,
                },
                ctxt.ctxt,
            )
        });

        logging::log!(
            LogPredicate::DebugBlock,
            ctxt,
            "loop_blocked_places: {}",
            loop_blocked_places.to_short_string(ctxt.ctxt)
        );

        let loop_blocker_places =
            live_loop_places.usages_where(|p| !p.place.regions(ctxt.ctxt).is_empty());

        logging::log!(
            LogPredicate::DebugBlock,
            ctxt,
            "loop_blocker_places: {}",
            loop_blocker_places.to_short_string(ctxt.ctxt)
        );

        let expand_places = loop_blocker_places.joined_with(&loop_blocked_places);

        self.expand_places_for_abstraction(
            &loop_blocked_places,
            &expand_places,
            validity_conditions,
            args.reborrow(),
            ctxt,
        );
        let capabilities = args.capabilities;
        self.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "G_Pre'",
            ctxt.ctxt,
        );

        // p_roots
        let live_roots = live_loop_places
            .iter()
            .flat_map(|p| self.get_borrow_roots(p.place, loop_head, ctxt.ctxt))
            .collect::<HashSet<_>>();

        logging::log!(
            LogPredicate::DebugBlock,
            ctxt,
            "live roots: {}",
            live_roots.to_short_string(ctxt.ctxt)
        );

        let root_places = live_roots
            .iter()
            .flat_map(|node| node.related_maybe_remote_current_place())
            .filter(|p| {
                !(p.is_local() && live_loop_places.contains(p.relevant_place_for_blocking()))
            })
            .collect::<HashSet<_>>();

        logging::log!(
            LogPredicate::DebugBlock,
            ctxt,
            "root places: {}",
            root_places.to_short_string(ctxt.ctxt)
        );

        let ConstructAbstractionGraphResult {
            graph: abstraction_graph,
            to_label,
            capability_updates,
        } = self.get_loop_abstraction_graph(
            &loop_blocked_places,
            root_places,
            &loop_blocker_places,
            loop_head,
            validity_conditions,
            ctxt,
        );

        abstraction_graph.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "Abstraction graph",
            ctxt.ctxt,
        );

        for rp in to_label.iter() {
            self.filter_mut_edges(|edge| {
                edge.label_lifetime_projection(
                    rp,
                    Some(LifetimeProjectionLabel::Location(SnapshotLocation::Loop(
                        loop_head,
                    ))),
                    ctxt.ctxt,
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

        let abstraction_graph_pcg_nodes = abstraction_graph.nodes(ctxt.ctxt);
        let to_cut =
            self.identify_subgraph_to_cut(loop_head, abstraction_graph_pcg_nodes, ctxt.ctxt);
        to_cut.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "To cut",
            ctxt.ctxt,
        );
        self.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "Self before cut",
            ctxt.ctxt,
        );
        for edge in to_cut.edges() {
            self.remove(edge.kind());
        }
        self.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "Self after cut",
            ctxt.ctxt,
        );
        for edge in abstraction_graph.into_edges() {
            self.insert(edge, ctxt.ctxt);
        }
        let self_places = self.places(ctxt.ctxt);
        for place in to_cut.places(ctxt.ctxt) {
            if !place.is_owned(ctxt.ctxt)
                && capabilities.get(place, ctxt.ctxt).is_some()
                && !self_places.contains(&place)
            {
                capabilities.remove(place, ctxt);
            }
        }
        self.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "Final graph",
            ctxt.ctxt,
        );
        Ok(())
    }
}
