use std::borrow::Cow;

use super::PcgError;
use crate::action::PcgAction;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike, LocalNode};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::graph::frozen::FrozenGraphRef;
use crate::free_pcs::CapabilityKind;
use crate::pcg::PCGNode;
use crate::pcg::obtain::PlaceObtainer;
use crate::pcg::place_capabilities::PlaceCapabilitiesInterface;
use crate::utils::HasPlace;
use crate::utils::Place;
use crate::utils::display::DisplayWithCompilerCtxt;

type EdgesToTrim<'tcx> = Vec<(BorrowPcgEdge<'tcx>, Cow<'static, str>)>;

impl<'pcg, 'mir: 'pcg, 'tcx> PlaceObtainer<'pcg, 'mir, 'tcx> {
    /// Removes leaves that are old or dead (based on the borrow checker). This
    /// function should called prior to evaluating the effect of the statement
    /// at `location`.
    ///
    /// Note that the liveness calculation is performed based on what happened
    /// at the end of the *previous* statement.
    ///
    /// For example when evaluating:
    /// ```text
    /// bb0[1]: let x = &mut y;
    /// bb0[2]: *x = 2;
    /// bb0[3]: ... // x is dead
    /// ```
    /// we do not remove the `*x -> y` edge until `bb0[3]`.
    /// This ensures that the edge appears in the graph at the end of `bb0[2]`
    /// (rather than never at all).
    ///
    /// Additional caveat: we do not remove dead places that are function
    /// arguments. At least for now this interferes with the implementation in
    /// the Prusti purified encoding for accessing the final value of a
    /// reference-typed function argument in its postcondition.
    pub(crate) fn pack_old_and_dead_borrow_leaves(
        &mut self,
        for_place: Option<Place<'tcx>>,
    ) -> Result<(), PcgError> {
        let debug_iteration_limit = 10000;
        let mut iteration = 0;
        self.restore_capability_to_leaf_places(for_place)?;
        loop {
            iteration += 1;
            let edges_to_trim = self.identify_edges_to_trim(for_place)?;
            if edges_to_trim.is_empty() {
                break Ok(());
            }
            for (edge, reason) in edges_to_trim {
                self.remove_edge_and_perform_associated_state_updates(
                    edge,
                    &format!(
                        "Trim Old Leaves (for place {:?}, iteration {}): {}",
                        for_place, iteration, reason
                    ),
                )?
            }
            if iteration % 10 == 0 {
                tracing::debug!(
                    "Packing old and dead borrow leaves: iteration {}",
                    iteration
                );
            }
            if iteration > debug_iteration_limit {
                panic!(
                    "Packing old and dead borrow leaves took more than {debug_iteration_limit} iterations"
                );
            }
        }
    }

    fn restore_capability_to_leaf_places(
        &mut self,
        parent_place: Option<Place<'tcx>>,
    ) -> Result<(), PcgError> {
        let leaf_places = self.pcg.leaf_places_where(
            |p| {
                self.pcg.capabilities.get(p) == Some(CapabilityKind::Read)
                    && !p.projects_shared_ref(self.ctxt)
                    && p.parent_place()
                        .is_none_or(|parent| self.pcg.capabilities.get(parent).is_none())
            },
            self.ctxt,
        );
        for place in leaf_places {
            if let Some(parent_place) = parent_place {
                if !parent_place.is_prefix_of(place) {
                    continue;
                }
            }
            let action = PcgAction::restore_capability(
                place,
                CapabilityKind::Exclusive,
                "restore capability to leaf place",
                self.ctxt,
            );
            self.record_and_apply_action(action)?;
        }
        Ok(())
    }

    /// Identifies the set of edges that should be removed from the graph
    ///
    /// If `ancestor_place` is defined, we only consider a subset of the edges.
    ///
    /// The subset of edges is defined as follows:
    ///
    /// A node *can be killed* if it has a related current place that is a
    /// postfix of `ancestor_place`.
    ///
    /// Then we consider edges where either:
    ///
    /// 1. The edge is an expansion edge, and the base can be killed, or
    /// 2. The edge is some other kind of edge, and all of the blocking nodes can be killed
    fn identify_edges_to_trim<'slf>(
        &'slf mut self,
        ancestor_place: Option<Place<'tcx>>,
    ) -> Result<EdgesToTrim<'tcx>, PcgError> {
        enum ShouldKillNode {
            Yes { reason: Cow<'static, str> },
            No,
        }

        let ctxt = self.ctxt;
        let location = self.location();

        let ancestor_predicate_allows_killing = |p: LocalNode<'tcx>| {
            let place = match p {
                PCGNode::Place(p) => p,
                PCGNode::RegionProjection(rp) => rp.place(),
            };
            if let Some(ancestor_place) = ancestor_place {
                if !place.is_current() || !ancestor_place.place().is_prefix_of(place.place()) {
                    return false;
                }
            }
            true
        };

        let should_kill_node = |p: LocalNode<'tcx>, fg: &FrozenGraphRef<'slf, 'tcx>| {
            let place = match p {
                PCGNode::Place(p) => p,
                PCGNode::RegionProjection(rp) => rp.place(),
            };
            if !ancestor_predicate_allows_killing(p) {
                return ShouldKillNode::No;
            }

            if place.is_old() {
                return ShouldKillNode::Yes {
                    reason: "Place is old".into(),
                };
            }

            if ctxt.is_arg(place.local()) {
                return ShouldKillNode::No;
            }

            if p.is_place()
                && !place.place().projection.is_empty()
                && !fg.has_edge_blocking(place.into(), ctxt)
            {
                return ShouldKillNode::Yes {
                    reason:
                        "Node is a place with a non-empty projection and is not blocked by an edge"
                            .into(),
                };
            }

            if ctxt.bc.is_dead(p.into(), location) {
                return ShouldKillNode::Yes {
                    reason: "Borrow-checker reports node as dead".into(),
                };
            }

            ShouldKillNode::No
        };

        enum ShouldPackEdge {
            Yes { reason: Cow<'static, str> },
            No,
        }

        let mut edges_to_trim = Vec::new();
        let fg = self.pcg.borrow.graph.frozen_graph();
        let location = self.location();
        let should_pack_edge = |edge: &BorrowPcgEdgeKind<'tcx>| match edge {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                if !ancestor_predicate_allows_killing(expansion.base()) {
                    return ShouldPackEdge::No;
                }
                if expansion.expansion().iter().all(|node| {
                    node.is_old() || self.ctxt.bc.is_dead(node.place().into(), location)
                }) {
                    ShouldPackEdge::Yes {
                        reason: "Expansion is old or dead".into(),
                    }
                } else if expansion.is_packable(self.pcg.capabilities) {
                    ShouldPackEdge::Yes {
                        reason: format!(
                            "Expansion {} is packable",
                            expansion.to_short_string(self.ctxt)
                        )
                        .into(),
                    }
                } else {
                    ShouldPackEdge::No
                }
            }
            _ => {
                let mut why_killed_reasons = Vec::new();
                for node in edge.blocked_by_nodes(self.ctxt) {
                    if let ShouldKillNode::Yes { reason } = should_kill_node(node, &fg) {
                        why_killed_reasons.push(format!(
                            "{}: {}",
                            node.to_short_string(self.ctxt),
                            reason
                        ));
                    } else {
                        tracing::debug!(
                            "Node {} will not be killed",
                            node.to_short_string(self.ctxt)
                        );
                        return ShouldPackEdge::No;
                    }
                }
                ShouldPackEdge::Yes {
                    reason: format!(
                        "Edge is blocked by nodes that should be killed: {}",
                        why_killed_reasons.join(", ")
                    )
                    .into(),
                }
            }
        };
        let leaf_edges = fg.leaf_edges(self.ctxt);
        // tracing::debug!("Leaf edges: {}", leaf_edges.to_short_string(self.ctxt));
        for edge in leaf_edges.into_iter().map(|e| e.to_owned_edge()) {
            tracing::debug!(
                "Checking leaf edge: {}",
                edge.kind.to_short_string(self.ctxt)
            );
            if let ShouldPackEdge::Yes { reason } = should_pack_edge(edge.kind()) {
                edges_to_trim.push((edge, reason));
            }
        }
        Ok(edges_to_trim)
    }
}
