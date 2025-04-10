use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BorrowPCGEdgeLike,
        edge::{kind::BorrowPCGEdgeKind, outlives::BorrowFlowEdgeKind},
        edge_data::EdgeData,
        graph::materialize::{MaterializedEdge, SyntheticEdge},
    },
    free_pcs::CapabilityKind,
    pcg::{MaybeHasLocation, PCGNode, PCGNodeLike},
    rustc_interface::middle::mir,
    utils::{maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace, CompilerCtxt, HasPlace},
};

use super::{graph_constructor::GraphConstructor, GraphEdge, NodeId};

pub(super) trait CapabilityGetter<'tcx> {
    fn get(&self, node: MaybeOldPlace<'tcx>) -> Option<CapabilityKind>;
}

pub(super) trait Grapher<'state, 'mir: 'state, 'tcx: 'mir> {
    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'state;
    fn insert_maybe_old_place(&mut self, place: MaybeOldPlace<'tcx>) -> NodeId {
        let capability_getter = self.capability_getter();
        let constructor = self.constructor();
        constructor.insert_place_node(place.place(), place.location(), &capability_getter)
    }
    fn insert_maybe_remote_place(&mut self, place: MaybeRemotePlace<'tcx>) -> NodeId {
        let constructor = self.constructor();
        match place {
            MaybeRemotePlace::Local(place) => self.insert_maybe_old_place(place),
            MaybeRemotePlace::Remote(local) => constructor.insert_remote_node(local),
        }
    }
    fn insert_pcg_node(&mut self, node: PCGNode<'tcx>) -> NodeId {
        match node {
            PCGNode::Place(place) => self.insert_maybe_remote_place(place),
            PCGNode::RegionProjection(rp) => self.constructor().insert_region_projection_node(rp),
        }
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'mir, 'tcx>;
    fn repacker(&self) -> CompilerCtxt<'mir, 'tcx>;
    fn draw_materialized_edge<'graph>(
        &mut self,
        edge: MaterializedEdge<'tcx, 'graph>,
        edge_idx: usize,
    ) where
        'mir: 'graph,
    {
        match edge {
            MaterializedEdge::Real(edge) => {
                self.draw_borrow_pcg_edge(edge, &self.capability_getter(), edge_idx)
            }
            MaterializedEdge::Synthetic(edge) => self.draw_synthetic_edge(edge),
        }
    }
    fn draw_synthetic_edge(&mut self, edge: SyntheticEdge<'tcx>) {
        match edge {
            SyntheticEdge::Alias(edge) => {
                let blocked_place = self.insert_pcg_node(edge.blocked_place);
                let blocking_place = self.insert_pcg_node(edge.blocking_place);
                self.constructor().edges.insert(GraphEdge::Alias {
                    blocked_place,
                    blocking_place,
                });
            }
        }
    }
    fn draw_borrow_pcg_edge(
        &mut self,
        edge: impl BorrowPCGEdgeLike<'tcx>,
        capabilities: &impl CapabilityGetter<'tcx>,
        edge_idx: usize,
    ) {
        match edge.kind() {
            BorrowPCGEdgeKind::BorrowPCGExpansion(deref_expansion) => {
                for blocked in deref_expansion.blocked_nodes(self.repacker()) {
                    let blocked_graph_node = self.insert_pcg_node(blocked);
                    for blocking in deref_expansion.blocked_by_nodes(self.repacker()) {
                        let blocking_graph_node = self.insert_pcg_node(blocking.into());
                        self.constructor().edges.insert(GraphEdge::DerefExpansion {
                            source: blocked_graph_node,
                            target: blocking_graph_node,
                            path_conditions: format!("{}", edge.conditions()),
                        });
                    }
                }
            }
            BorrowPCGEdgeKind::Borrow(borrow) => {
                let borrowed_place = self.insert_maybe_remote_place(borrow.blocked_place());
                let assigned_region_projection = borrow
                    .assigned_region_projection(self.repacker())
                    .to_region_projection(self.repacker());
                let assigned_rp_node = self
                    .constructor()
                    .insert_region_projection_node(assigned_region_projection);
                let kind = match borrow.kind() {
                    Some(mir::BorrowKind::Shared) => "shared".to_string(),
                    Some(mir::BorrowKind::Mut { kind }) => format!("{:?}", kind),
                    Some(mir::BorrowKind::Fake(_)) => "fake".to_string(),
                    None => "".to_string(),
                };
                self.constructor().edges.insert(GraphEdge::Borrow {
                    borrowed_place,
                    assigned_region_projection: assigned_rp_node,
                    location: borrow.reserve_location(),
                    region: borrow.borrow_region().map(|r| format!("{:?}", r)),
                    path_conditions: format!("{}", edge.conditions()),
                    kind,
                });
            }
            BorrowPCGEdgeKind::Abstraction(abstraction) => {
                self.constructor()
                    .insert_abstraction(abstraction, capabilities, edge_idx);
            }
            BorrowPCGEdgeKind::BorrowFlow(member) => {
                let input_node = self.insert_pcg_node(member.long().into());
                let output_node = self.insert_pcg_node(member.short().to_pcg_node(self.repacker()));
                self.constructor().edges.insert(GraphEdge::BorrowFlow {
                    source: input_node,
                    target: output_node,
                    kind: format!("{}", member.kind),
                    regions_equal: matches!(member.kind(), BorrowFlowEdgeKind::BorrowOutlives { regions_equal, .. } if regions_equal),
                });
            }
        }
    }
}
