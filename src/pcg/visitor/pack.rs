use std::borrow::Cow;

use super::PcgError;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike, LocalNode};
use crate::borrow_pcg::edge::deref::DerefEdge;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::graph::Conditioned;
use crate::borrow_pcg::graph::frozen::FrozenGraphRef;
use crate::pcg::PcgNode;
use crate::pcg::obtain::{PlaceCollapser, PlaceObtainer};
use crate::utils::HasPlace;
use crate::utils::data_structures::{HashMap, HashSet};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::maybe_old::MaybeLabelledPlace;
use crate::utils::{DataflowCtxt, Place};

type Reason = Cow<'static, str>;

struct WithReason<T> {
    pub(crate) value: T,
    pub(crate) reason: Reason,
}

struct EdgesToRemove<'tcx> {
    deref_edges:
        HashMap<MaybeLabelledPlace<'tcx>, WithReason<HashSet<Conditioned<DerefEdge<'tcx>>>>>,
    other_edges: Vec<WithReason<BorrowPcgEdge<'tcx>>>,
}

enum RemovalAction<'tcx> {
    RemoveDerefEdgesTo(
        MaybeLabelledPlace<'tcx>,
        HashSet<Conditioned<DerefEdge<'tcx>>>,
        Reason,
    ),
    RemoveOtherEdge(BorrowPcgEdge<'tcx>, Reason),
}

impl<'tcx> EdgesToRemove<'tcx> {
    fn new() -> Self {
        Self {
            deref_edges: HashMap::default(),
            other_edges: Vec::new(),
        }
    }

    fn push(&mut self, edge: BorrowPcgEdge<'tcx>, reason: Reason) {
        match edge.kind() {
            BorrowPcgEdgeKind::Deref(deref) => {
                if let Some(deref_edges) = self.deref_edges.get_mut(&deref.deref_place) {
                    deref_edges
                        .value
                        .insert(Conditioned::new(*deref, edge.conditions().clone()));
                } else {
                    self.deref_edges.insert(deref.deref_place, WithReason {
                        value: vec![Conditioned::new(*deref, edge.conditions().clone())]
                            .into_iter()
                            .collect(),
                        reason,
                    });
                }
            }
            _ => self.other_edges.push(WithReason {
                value: edge.clone(),
                reason,
            }),
        }
    }

    fn is_empty(&self) -> bool {
        self.deref_edges.is_empty() && self.other_edges.is_empty()
    }

    fn removal_actions(self) -> Vec<RemovalAction<'tcx>> {
        let mut actions = Vec::new();
        for (place, deref_edges) in self.deref_edges.into_iter() {
            actions.push(RemovalAction::RemoveDerefEdgesTo(
                place,
                deref_edges.value,
                deref_edges.reason,
            ));
        }
        for edge in self.other_edges.into_iter() {
            actions.push(RemovalAction::RemoveOtherEdge(edge.value, edge.reason));
        }
        actions
    }
}

impl<'pcg, 'a: 'pcg, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PlaceObtainer<'pcg, 'a, 'tcx, Ctxt> {
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
        self.restore_capability_to_leaf_places(for_place, self.ctxt)?;
        loop {
            iteration += 1;
            let edges_to_remove = self.identify_leaf_edges_to_remove(for_place)?;
            if edges_to_remove.is_empty() {
                break Ok(());
            }
            for action in edges_to_remove.removal_actions() {
                match action {
                    RemovalAction::RemoveDerefEdgesTo(place, edges, reason) => {
                        self.remove_deref_edges_to(place, edges, &reason)?;
                    }
                    RemovalAction::RemoveOtherEdge(borrow_pcg_edge, reason) => {
                        self.remove_edge_and_perform_associated_state_updates(
                            &borrow_pcg_edge,
                            &reason,
                        )?;
                    }
                }
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
    fn identify_leaf_edges_to_remove<'slf>(
        &'slf mut self,
        ancestor_place: Option<Place<'tcx>>,
    ) -> Result<EdgesToRemove<'tcx>, PcgError> {
        enum ShouldKillNode {
            Yes { reason: Cow<'static, str> },
            No,
        }

        let ctxt = self.ctxt;
        let location = self.location();

        let ancestor_predicate_allows_killing = |p: LocalNode<'tcx>| {
            let place = match p {
                PcgNode::Place(p) => p,
                PcgNode::LifetimeProjection(rp) => rp.place(),
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
                PcgNode::Place(p) => p,
                PcgNode::LifetimeProjection(rp) => rp.place(),
            };
            if !ancestor_predicate_allows_killing(p) {
                return ShouldKillNode::No;
            }

            if place.is_old() {
                return ShouldKillNode::Yes {
                    reason: "Place is old".into(),
                };
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

            if ctxt.bc().is_dead(p.into(), location) {
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

        let mut edges_to_remove = EdgesToRemove::new();
        let fg = self.pcg.borrow.graph.frozen_graph();
        let location = self.location();
        let should_pack_edge = |edge: &BorrowPcgEdgeKind<'tcx>| match edge {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                if !ancestor_predicate_allows_killing(expansion.base()) {
                    return ShouldPackEdge::No;
                }
                if expansion.expansion().iter().all(|node| {
                    node.is_old() || self.ctxt.bc().is_dead(node.place().into(), location)
                }) {
                    ShouldPackEdge::Yes {
                        reason: "Expansion is old or dead".into(),
                    }
                } else if expansion.is_packable(self.pcg.capabilities, self.ctxt) {
                    ShouldPackEdge::Yes {
                        reason: format!(
                            "Expansion {} is packable",
                            expansion.to_short_string(self.ctxt.bc_ctxt())
                        )
                        .into(),
                    }
                } else {
                    ShouldPackEdge::No
                }
            }
            _ => {
                let mut why_killed_reasons = Vec::new();
                for node in edge.blocked_by_nodes(self.ctxt.bc_ctxt()) {
                    if let ShouldKillNode::Yes { reason } = should_kill_node(node, &fg) {
                        why_killed_reasons.push(format!(
                            "{}: {}",
                            node.to_short_string(self.ctxt.bc_ctxt()),
                            reason
                        ));
                    } else {
                        tracing::debug!(
                            "Node {} will not be killed",
                            node.to_short_string(self.ctxt.bc_ctxt())
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
                edge.kind.to_short_string(self.ctxt.bc_ctxt())
            );
            if let ShouldPackEdge::Yes { reason } = should_pack_edge(edge.kind()) {
                edges_to_remove.push(edge, reason);
            }
        }
        Ok(edges_to_remove)
    }
}
