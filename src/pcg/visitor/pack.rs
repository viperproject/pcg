use itertools::Itertools;

use super::PcgVisitor;
use super::{Pcg, PcgError};
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPCGEdge, BorrowPCGEdgeLike, LocalNode};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::graph::frozen::FrozenGraphRef;
use crate::free_pcs::CapabilityKind;
use crate::pcg::{MaybeHasLocation, PCGNode};
use crate::rustc_interface::middle::mir::Location;
use crate::utils::{CompilerCtxt, HasPlace};

impl PcgVisitor<'_, '_, '_> {
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
        location: Location,
    ) -> Result<(), PcgError> {
        let mut num_edges_prev = self.pcg.borrow.graph().num_edges();
        loop {
            fn go<'slf, 'mir: 'slf, 'bc: 'slf, 'tcx>(
                slf: &'slf mut Pcg<'tcx>,
                ctxt: CompilerCtxt<'mir, 'tcx>,
                location: Location,
            ) -> Vec<BorrowPCGEdge<'tcx>> {
                let fg = slf.borrow.graph().frozen_graph();

                let should_kill_node = |p: LocalNode<'tcx>, fg: &FrozenGraphRef<'slf, 'tcx>| {
                    let place = match p {
                        PCGNode::Place(p) => p,
                        PCGNode::RegionProjection(rp) => rp.place(),
                    };
                    if place.is_old() {
                        return true;
                    }

                    if ctxt.is_arg(place.local()) {
                        return false;
                    }

                    if !place.place().projection.is_empty()
                        && !fg.has_edge_blocking(place.into(), ctxt)
                    {
                        return true;
                    }

                    ctxt.bc.is_dead(p.into(), location, true) // Definitely a leaf by this point
                };

                let should_pack_edge = |edge: &BorrowPcgEdgeKind<'tcx>| match edge {
                    BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                        if expansion.expansion().iter().all(|node| {
                            node.is_old() || ctxt.bc.is_dead(node.place().into(), location, true)
                        }) {
                            true
                        } else {
                            expansion.expansion().iter().all(|node| {
                                expansion.base().place().is_prefix_exact(node.place())
                                    && expansion.base().location() == node.location()
                            })
                        }
                    }
                    _ => edge
                        .blocked_by_nodes(ctxt)
                        .iter()
                        .all(|p| should_kill_node(*p, &fg)),
                };

                let mut edges_to_trim = Vec::new();
                for edge in fg.leaf_edges(ctxt).into_iter().map(|e| e.to_owned_edge()) {
                    if should_pack_edge(edge.kind()) {
                        edges_to_trim.push(edge);
                    }
                }
                edges_to_trim
            }
            let edges_to_trim = go(self.pcg, self.ctxt, location);
            if edges_to_trim.is_empty() {
                break Ok(());
            }
            for edge in edges_to_trim {
                self.remove_edge_and_set_latest(edge, location, "Trim Old Leaves")?
            }
            let new_num_edges = self.pcg.borrow.graph().num_edges();
            assert!(new_num_edges <= num_edges_prev);
            num_edges_prev = new_num_edges;
        }
    }

    pub(crate) fn collapse_owned_places(&mut self) -> Result<(), PcgError> {
        for caps in self
            .pcg
            .owned
            .data
            .clone()
            .unwrap()
            .capability_projections()
        {
            let mut expansions = caps
                .expansions()
                .clone()
                .into_iter()
                .sorted_by_key(|(p, _)| p.projection.len())
                .collect::<Vec<_>>();
            while let Some((base, expansion)) = expansions.pop() {
                let expansion_places = base.expansion_places(&expansion, self.ctxt);
                if expansion_places
                    .iter()
                    .all(|p| !self.pcg.borrow.graph().contains(*p, self.ctxt))
                    && let Some(candidate_cap) =
                        self.pcg.capabilities.get(expansion_places[0].into())
                    && expansion_places
                        .iter()
                        .all(|p| self.pcg.capabilities.get((*p).into()) == Some(candidate_cap))
                {
                    self.collapse(base, candidate_cap)?;
                    if base.projection.is_empty()
                        && self.pcg.capabilities.get(base.into()) == Some(CapabilityKind::Read)
                    {
                        self.pcg
                            .capabilities
                            .insert(base.into(), CapabilityKind::Exclusive);
                    }
                }
            }
        }
        Ok(())
    }
}
