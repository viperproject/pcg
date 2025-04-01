use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeLike, LocalNode},
        edge::kind::BorrowPCGEdgeKind,
        graph::materialize::{MaterializedEdge, SyntheticEdge},
    },
    pcg::{LocalNodeLike, MaybeHasLocation, PCGNode, PCGNodeLike},
    free_pcs::CapabilityKind,
    rustc_interface::middle::mir,
    utils::{maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace, HasPlace, PlaceRepacker},
};

use super::{graph_constructor::GraphConstructor, GraphEdge, NodeId};

pub(super) trait CapabilityGetter<'tcx> {
    fn get(&self, node: MaybeOldPlace<'tcx>) -> Option<CapabilityKind>;
}

pub(super) trait Grapher<'mir, 'tcx: 'mir> {
    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'mir;
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

    fn insert_local_node(&mut self, node: LocalNode<'tcx>) -> NodeId {
        match node {
            LocalNode::Place(place) => self.insert_maybe_old_place(place),
            LocalNode::RegionProjection(rp) => {
                let rp = rp.to_region_projection(self.repacker());
                self.constructor().insert_region_projection_node(rp)
            }
        }
    }
    fn constructor(&mut self) -> &mut GraphConstructor<'mir, 'tcx>;
    fn repacker(&self) -> PlaceRepacker<'mir, 'tcx>;
    fn draw_materialized_edge<'graph>(&mut self, edge: MaterializedEdge<'tcx, 'graph>)
    where
        'mir: 'graph,
    {
        match edge {
            MaterializedEdge::Real(edge) => {
                self.draw_borrow_pcg_edge(edge, &self.capability_getter())
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
    ) {
        match edge.kind() {
            BorrowPCGEdgeKind::BorrowPCGExpansion(deref_expansion) => {
                let base_node = self.insert_local_node(deref_expansion.base);
                for place in deref_expansion.expansion.iter() {
                    let expansion_node = self.insert_local_node(*place);
                    self.constructor().edges.insert(GraphEdge::DerefExpansion {
                        source: base_node,
                        target: expansion_node,
                        path_conditions: format!("{}", edge.conditions()),
                    });
                    if deref_expansion.is_deref_of_borrow(self.repacker())
                        && let PCGNode::Place(base) = deref_expansion.base
                    {
                        let base_rp = self.insert_local_node(
                            base.base_region_projection(self.repacker()).unwrap().into(),
                        );
                        self.constructor().edges.insert(GraphEdge::Block {
                            source: base_rp,
                            target: expansion_node,
                            kind: "".to_string(),
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
                    .insert_abstraction(abstraction, capabilities);
            }
            BorrowPCGEdgeKind::Outlives(member) => {
                let input_node = self.insert_pcg_node(member.long().into());
                let output_node = self.insert_pcg_node(member.short().to_pcg_node(self.repacker()));
                self.constructor().edges.insert(GraphEdge::Block {
                    source: input_node,
                    target: output_node,
                    kind: format!("{}", member.kind),
                });
            }
            BorrowPCGEdgeKind::RegionProjectionMember(member) => {
                let input_node = self.insert_pcg_node(member.blocked_node());
                let output_node = self.insert_local_node(member.blocked_by_node(self.repacker()));
                self.constructor().edges.insert(GraphEdge::Block {
                    source: input_node,
                    target: output_node,
                    kind: format!("{:?}", member.direction()),
                });
            }
            BorrowPCGEdgeKind::FunctionCallRegionCoupling(edge) => {
                let input_nodes = edge
                    .inputs
                    .iter()
                    .map(|rp| self.insert_local_node(rp.to_local_node(self.repacker())))
                    .collect::<Vec<_>>();
                let output_nodes = edge
                    .outputs
                    .iter()
                    .map(|rp| self.insert_local_node(rp.to_local_node(self.repacker())))
                    .collect::<Vec<_>>();
                let mut i = 0;
                while i < edge.num_coupled_nodes() {
                    self.constructor().edges.insert(GraphEdge::Coupled {
                        source: input_nodes[i],
                        target: output_nodes[i],
                        directed: true,
                    });
                    if i < edge.num_coupled_nodes() - 1 {
                        self.constructor().edges.insert(GraphEdge::Coupled {
                            source: input_nodes[i],
                            target: input_nodes[i + 1],
                            directed: false,
                        });
                        self.constructor().edges.insert(GraphEdge::Coupled {
                            source: output_nodes[i],
                            target: output_nodes[i + 1],
                            directed: false,
                        });
                    }
                    let mut j = 0;
                    while j < edge.num_coupled_nodes() {
                        self.constructor().edges.insert(GraphEdge::Coupled {
                            source: input_nodes[i],
                            target: output_nodes[j],
                            directed: true,
                        });
                        j += 1;
                    }
                    i += 1;
                }
            }
        }
    }
}
