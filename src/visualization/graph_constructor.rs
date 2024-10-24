use crate::{
    borrows::{
        borrows_edge::{BorrowsEdge, BorrowsEdgeKind},
        borrows_graph::BorrowsGraph,
        borrows_state::BorrowsState,
        deref_expansion::DerefExpansion,
        domain::{
            AbstractionInputTarget, AbstractionOutputTarget, MaybeOldPlace, MaybeRemotePlace,
            RemotePlace,
        },
        region_abstraction::AbstractionEdge,
        region_projection::RegionProjection,
        unblock_graph::UnblockGraph,
    },
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary},
    rustc_interface::{self, middle::mir::Local},
    utils::{Place, PlaceRepacker, PlaceSnapshot, SnapshotLocation},
    visualization::dot_graph::RankAnnotation,
};

use std::{
    borrow::Borrow,
    collections::{BTreeSet, HashSet},
    ops::Deref,
};

use rustc_interface::middle::ty::{self, TyCtxt};

use super::{dot_graph::DotSubgraph, Graph, GraphEdge, GraphNode, NodeId, NodeType};

#[derive(Eq, PartialEq, Hash)]
pub struct GraphCluster {
    label: String,
    id: String,
    nodes: BTreeSet<NodeId>,
    min_rank_nodes: Option<BTreeSet<NodeId>>,
}

impl GraphCluster {
    pub fn to_dot_subgraph(&self, nodes: &[GraphNode]) -> DotSubgraph {
        DotSubgraph {
            id: format!("cluster_{}", self.id),
            label: self.label.clone(),
            nodes: self
                .nodes
                .iter()
                .map(|node_id| {
                    nodes
                        .iter()
                        .find(|n| n.id == *node_id)
                        .unwrap()
                        .to_dot_node()
                })
                .collect(),
            rank_annotations: self
                .min_rank_nodes
                .as_ref()
                .map(|nodes| {
                    vec![RankAnnotation {
                        rank_type: "min".to_string(),
                        nodes: nodes.iter().map(|n| n.to_string()).collect(),
                    }]
                })
                .unwrap_or_default(),
        }
    }
}

struct GraphConstructor<'mir, 'tcx> {
    remote_nodes: IdLookup<RemotePlace>,
    place_nodes: IdLookup<(Place<'tcx>, Option<SnapshotLocation>)>,
    region_projection_nodes: IdLookup<RegionProjection<'tcx>>,
    region_clusters: HashSet<GraphCluster>,
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
    repacker: PlaceRepacker<'mir, 'tcx>,
}

struct IdLookup<T>(char, Vec<T>);

impl<T: Eq + Clone> IdLookup<T> {
    fn new(prefix: char) -> Self {
        Self(prefix, vec![])
    }

    fn existing_id(&mut self, item: &T) -> Option<NodeId> {
        self.1
            .iter()
            .position(|x| x == item)
            .map(|idx| NodeId(self.0, idx))
    }

    fn node_id(&mut self, item: &T) -> NodeId {
        if let Some(idx) = self.existing_id(item) {
            idx
        } else {
            self.1.push(item.clone());
            NodeId(self.0, self.1.len() - 1)
        }
    }
}

impl<'a, 'tcx> GraphConstructor<'a, 'tcx> {
    fn new(repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            remote_nodes: IdLookup::new('a'),
            place_nodes: IdLookup::new('p'),
            region_projection_nodes: IdLookup::new('r'),
            region_clusters: HashSet::new(),
            nodes: vec![],
            edges: HashSet::new(),
            repacker,
        }
    }

    fn to_graph(self) -> Graph {
        Graph::new(self.nodes, self.edges, self.region_clusters)
    }

    fn place_node_id(&mut self, place: Place<'tcx>, location: Option<SnapshotLocation>) -> NodeId {
        self.place_nodes.node_id(&(place, location))
    }

    fn insert_node(&mut self, node: GraphNode) {
        if !self.nodes.contains(&node) {
            self.nodes.push(node);
        }
    }

    fn insert_abstraction_input_target(&mut self, target: AbstractionInputTarget<'tcx>) -> NodeId {
        self.insert_region_projection_node(target)
    }

    fn insert_abstraction_output_target(
        &mut self,
        target: AbstractionOutputTarget<'tcx>,
    ) -> NodeId {
        self.insert_region_projection_node(target)
    }

    fn insert_region_projection_and_ancestors(
        &mut self,
        projection: RegionProjection<'tcx>,
    ) -> NodeId {
        let node = self.insert_region_projection_node(projection);
        let mut last_node = node;
        let mut last_projection = projection;
        while let Some(projection) = last_projection.prefix_projection(self.repacker) {
            let node = self.insert_region_projection_node(projection);
            self.edges.insert(GraphEdge::ProjectionEdge {
                source: node,
                target: last_node,
            });
            last_node = node;
            last_projection = projection;
        }
        node
    }

    fn insert_region_projection_node(&mut self, projection: RegionProjection<'tcx>) -> NodeId {
        if let Some(id) = self.region_projection_nodes.existing_id(&projection) {
            return id;
        }
        let id = self.region_projection_nodes.node_id(&projection);
        let node = GraphNode {
            id,
            node_type: NodeType::RegionProjectionNode {
                label: format!(
                    "{}↓{:?}",
                    projection.place.to_short_string(self.repacker),
                    projection.region()
                ),
            },
        };
        self.insert_node(node);
        id
    }

    fn insert_region_abstraction(&mut self, region_abstraction: &AbstractionEdge<'tcx>) {
        let mut input_nodes = BTreeSet::new();
        let mut output_nodes = BTreeSet::new();

        for edge in region_abstraction.edges() {
            for input in edge.inputs() {
                let input = self.insert_abstraction_input_target(input);
                input_nodes.insert(input);
            }
            for output in edge.outputs() {
                let output = self.insert_abstraction_output_target(output);
                output_nodes.insert(output);
            }
            for input in &input_nodes {
                for output in &output_nodes {
                    // TODO: Color or Label edges
                    self.edges.insert(GraphEdge::AbstractEdge {
                        blocked: *input,
                        blocking: *output,
                    });
                }
            }
        }

        assert!(!input_nodes.is_empty());
        let cluster = GraphCluster {
            id: format!(
                "c{:?}_{}",
                region_abstraction.location().block,
                region_abstraction.location().statement_index
            ),
            label: format!("{:?}", region_abstraction.location()),
            nodes: input_nodes
                .iter()
                .chain(output_nodes.iter())
                .cloned()
                .collect(),
            min_rank_nodes: Some(input_nodes),
        };
        self.region_clusters.insert(cluster);
    }

    fn insert_remote_node(&mut self, remote_place: RemotePlace) -> NodeId {
        if let Some(id) = self.remote_nodes.existing_id(&remote_place) {
            return id;
        }
        let id = self.remote_nodes.node_id(&remote_place);
        let node = GraphNode {
            id,
            node_type: NodeType::ReborrowingDagNode {
                label: format!("Target of input {:?}", remote_place.assigned_local()),
                location: None,
            },
        };
        self.insert_node(node);
        id
    }

    fn insert_place_node(
        &mut self,
        place: Place<'tcx>,
        location: Option<SnapshotLocation>,
        capability: Option<CapabilityKind>,
    ) -> NodeId {
        if let Some(node_id) = self.place_nodes.existing_id(&(place, location)) {
            return node_id;
        }
        let id = self.place_node_id(place, location);
        let label = format!("{:?}", place.to_string(self.repacker));
        let region = match place.ty(self.repacker).ty.kind() {
            ty::TyKind::Ref(region, _, _) => Some(format!("{:?}", region)),
            _ => None,
        };
        let node_type = if place.is_owned(self.repacker.body(), self.repacker.tcx()) {
            NodeType::FPCSNode {
                label,
                capability,
                location,
                region,
            }
        } else {
            assert!(capability.is_none());
            NodeType::ReborrowingDagNode { label, location }
        };
        if place.is_owned(self.repacker.body(), self.repacker.tcx()) {
            for region_projection in place.region_projections(self.repacker) {
                self.insert_region_projection_and_ancestors(region_projection);
            }
        }
        let node = GraphNode { id, node_type };
        self.insert_node(node);
        id
    }
}

pub struct UnblockGraphConstructor<'a, 'tcx> {
    unblock_graph: UnblockGraph<'tcx>,
    constructor: GraphConstructor<'a, 'tcx>,
}

impl<'a, 'tcx> UnblockGraphConstructor<'a, 'tcx> {
    pub fn new(unblock_graph: UnblockGraph<'tcx>, repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            unblock_graph,
            constructor: GraphConstructor::new(repacker),
        }
    }

    pub fn construct_graph(mut self) -> Graph {
        for edge in self.unblock_graph.edges().cloned().collect::<Vec<_>>() {
            self.draw_borrows_edge(&edge, None);
        }
        self.constructor.to_graph()
    }
}

impl<'mir, 'tcx> PlaceGrapher<'mir, 'tcx> for UnblockGraphConstructor<'mir, 'tcx> {
    fn insert_maybe_old_place(&mut self, place: MaybeOldPlace<'tcx>) -> NodeId {
        self.constructor
            .insert_place_node(place.place(), place.location(), None)
    }

    fn insert_maybe_remote_place(&mut self, place: MaybeRemotePlace<'tcx>) -> NodeId {
        match place {
            MaybeRemotePlace::Local(place) => self.insert_maybe_old_place(place),
            MaybeRemotePlace::Remote(local) => self.constructor.insert_remote_node(local),
        }
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'mir, 'tcx> {
        &mut self.constructor
    }

    fn repacker(&self) -> PlaceRepacker<'mir, 'tcx> {
        self.constructor.repacker
    }
}

trait PlaceGrapher<'mir, 'tcx: 'mir> {
    fn insert_maybe_remote_place(&mut self, place: MaybeRemotePlace<'tcx>) -> NodeId;
    fn insert_maybe_old_place(&mut self, place: MaybeOldPlace<'tcx>) -> NodeId;
    fn constructor(&mut self) -> &mut GraphConstructor<'mir, 'tcx>;
    fn repacker(&self) -> PlaceRepacker<'mir, 'tcx>;
    fn draw_borrows_edge(&mut self, edge: &BorrowsEdge<'tcx>, graph: Option<&BorrowsGraph<'tcx>>) {
        match edge.kind() {
            BorrowsEdgeKind::DerefExpansion(deref_expansion) => {
                let base_node = self.insert_maybe_old_place(deref_expansion.base());
                match deref_expansion {
                    DerefExpansion::OwnedExpansion(owned) => {
                        let target = self.insert_maybe_old_place(owned.expansion(self.repacker()));
                        self.constructor()
                            .edges
                            .insert(GraphEdge::DerefExpansionEdge {
                                source: base_node,
                                target,
                                path_conditions: format!("{}", edge.conditions()),
                            });
                        // TODO: Region could be erased and we can't handle that yet
                        if owned.base().has_region_projections(self.repacker()) {
                            let base_rp = owned.base_region_projection(self.repacker());
                            let base_rp_node = self
                                .constructor()
                                .insert_region_projection_and_ancestors(base_rp);
                            self.constructor().edges.insert(
                                GraphEdge::RegionProjectionToDerefExpansionEdge {
                                    region_projection: base_rp_node,
                                    deref: target,
                                },
                            );
                        }
                    }
                    _ => {
                        for place in deref_expansion.expansion(self.repacker()) {
                            let place = self.insert_maybe_old_place(place);
                            self.constructor()
                                .edges
                                .insert(GraphEdge::DerefExpansionEdge {
                                    source: base_node,
                                    target: place,
                                    path_conditions: format!("{}", edge.conditions()),
                                });
                        }
                    }
                }
            }
            BorrowsEdgeKind::Reborrow(reborrow) => {
                let borrowed_place = self.insert_maybe_remote_place(reborrow.blocked_place);
                // TODO: Region could be erased and we can't handle that yet
                if let Some(assigned_region_projection) =
                    reborrow.assigned_region_projection(self.repacker())
                {
                    let assigned_place = self
                        .constructor()
                        .insert_region_projection_and_ancestors(assigned_region_projection);
                    self.constructor().edges.insert(GraphEdge::ReborrowEdge {
                        borrowed_place,
                        assigned_place,
                        location: reborrow.reserve_location(),
                        region: format!("{:?}", reborrow.region),
                        path_conditions: format!("{}", edge.conditions()),
                    });
                }
            }
            BorrowsEdgeKind::Abstraction(abstraction) => {
                let _r = self.constructor().insert_region_abstraction(abstraction);
            }
            BorrowsEdgeKind::RegionProjectionMember(member) => {
                let place = self.insert_maybe_remote_place(member.place);
                let region_projection = self
                    .constructor()
                    .insert_region_projection_node(member.projection);
                self.constructor()
                    .edges
                    .insert(GraphEdge::RegionProjectionMemberEdge {
                        place,
                        region_projection,
                    });
            }
        }
    }
}

pub struct PCSGraphConstructor<'a, 'tcx> {
    summary: &'a CapabilitySummary<'tcx>,
    borrows_domain: &'a BorrowsState<'tcx>,
    constructor: GraphConstructor<'a, 'tcx>,
    repacker: PlaceRepacker<'a, 'tcx>,
}

impl<'a, 'tcx> PlaceGrapher<'a, 'tcx> for PCSGraphConstructor<'a, 'tcx> {
    fn repacker(&self) -> PlaceRepacker<'a, 'tcx> {
        self.repacker
    }

    fn insert_maybe_old_place(&mut self, place: MaybeOldPlace<'tcx>) -> NodeId {
        match place {
            MaybeOldPlace::Current { place } => {
                self.constructor
                    .insert_place_node(place, None, self.capability_for_place(place))
            }
            MaybeOldPlace::OldPlace(snapshot_place) => self.insert_snapshot_place(snapshot_place),
        }
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'a, 'tcx> {
        &mut self.constructor
    }

    fn insert_maybe_remote_place(&mut self, place: MaybeRemotePlace<'tcx>) -> NodeId {
        match place {
            MaybeRemotePlace::Local(place) => self.insert_maybe_old_place(place),
            MaybeRemotePlace::Remote(local) => self.constructor.insert_remote_node(local),
        }
    }
}

impl<'a, 'tcx> PCSGraphConstructor<'a, 'tcx> {
    pub fn new(
        summary: &'a CapabilitySummary<'tcx>,
        repacker: PlaceRepacker<'a, 'tcx>,
        borrows_domain: &'a BorrowsState<'tcx>,
    ) -> Self {
        Self {
            summary,
            borrows_domain,
            constructor: GraphConstructor::new(repacker),
            repacker,
        }
    }

    fn insert_place_and_previous_projections(
        &mut self,
        place: Place<'tcx>,
        location: Option<SnapshotLocation>,
        kind: Option<CapabilityKind>,
    ) -> NodeId {
        let node = self.constructor.insert_place_node(place, location, kind);
        if location.is_some() {
            return node;
        }
        let mut projection = place.projection;
        let mut last_node = node;
        let mut last_place = place.into();
        while !projection.is_empty() {
            projection = &projection[..projection.len() - 1];
            let place = Place::new(place.local, &projection);
            let connections = RegionProjection::connections_between_places(
                place.into(),
                last_place,
                self.repacker,
            );
            for (rp1, rp2) in connections {
                let source = self.constructor.insert_region_projection_and_ancestors(rp1);
                let target = self.constructor.insert_region_projection_and_ancestors(rp2);
                self.constructor
                    .edges
                    .insert(GraphEdge::ProjectionEdge { source, target });
            }
            last_place = place.into();
            let node = self.constructor.insert_place_node(place, None, None);
            self.constructor.edges.insert(GraphEdge::ProjectionEdge {
                source: node,
                target: last_node,
            });
            last_node = node.clone();
        }
        node
    }

    fn insert_snapshot_place(&mut self, place: PlaceSnapshot<'tcx>) -> NodeId {
        let cap = self.capability_for_place(place.place);
        self.insert_place_and_previous_projections(place.place, Some(place.at), cap)
    }

    fn capability_for_place(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        match self.summary.get(place.local) {
            Some(CapabilityLocal::Allocated(projections)) => {
                projections.deref().get(&place).cloned()
            }
            _ => None,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.constructor.repacker.tcx()
    }

    pub fn construct_graph(mut self) -> Graph {
        for (_local, capability) in self.summary.iter().enumerate() {
            match capability {
                CapabilityLocal::Unallocated => {}
                CapabilityLocal::Allocated(projections) => {
                    for (place, kind) in projections.iter() {
                        self.insert_place_and_previous_projections(*place, None, Some(*kind));
                    }
                }
            }
        }
        for edge in self.borrows_domain.graph_edges() {
            self.draw_borrows_edge(edge, Some(self.borrows_domain.graph()));
        }

        self.constructor.to_graph()
    }
}
