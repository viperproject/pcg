use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeLike, LocalNode},
        coupling_graph_constructor::CGNode,
        graph::BorrowsGraph,
        region_projection::RegionProjection,
        state::BorrowsState,
    },
    combined_pcs::{PCGNode, PCGNodeLike},
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary},
    utils::{
        display::DisplayWithRepacker, HasPlace, Place, PlaceRepacker, PlaceSnapshot,
        SnapshotLocation,
    },
    visualization::dot_graph::RankAnnotation,
};

use super::{dot_graph::DotSubgraph, Graph, GraphEdge, GraphNode, NodeId, NodeType};
use crate::borrow_pcg::edge::abstraction::AbstractionType;
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::rustc_interface::middle::ty::TyCtxt;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::place::remote::RemotePlace;
use std::collections::{BTreeSet, HashSet};

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

    fn into_graph(self) -> Graph {
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

    fn insert_region_projection_node(
        &mut self,
        projection: RegionProjection<'tcx>,
        capability: Option<CapabilityKind>,
    ) -> NodeId {
        if let Some(id) = self.region_projection_nodes.existing_id(&projection) {
            return id;
        }
        let id = self.region_projection_nodes.node_id(&projection);
        let node = GraphNode {
            id,
            node_type: NodeType::RegionProjectionNode {
                label: format!(
                    "{}↓{}{}",
                    projection.place().to_short_string(self.repacker),
                    projection.region(self.repacker),
                    if let Some(capability) = capability {
                        format!(" {:?}", capability)
                    } else {
                        "".to_string()
                    }
                ),
            },
        };
        self.insert_node(node);
        id
    }

    fn insert_cg_node(&mut self, node: CGNode<'tcx>, capability: Option<CapabilityKind>) -> NodeId {
        match node {
            CGNode::RegionProjection(rp) => self.insert_region_projection_node(rp, capability),
            CGNode::RemotePlace(rp) => self.insert_remote_node(rp, capability),
        }
    }

    fn insert_abstraction(
        &mut self,
        abstraction: &AbstractionType<'tcx>,
        capabilities: &impl CapabilityGetter<'tcx>,
    ) {
        let mut input_nodes = BTreeSet::new();
        let mut output_nodes = BTreeSet::new();

        for input in abstraction.inputs() {
            let input = self.insert_cg_node(input, capabilities.get(input.into()));
            input_nodes.insert(input);
        }

        for output in abstraction.outputs() {
            let output = output.set_base(output.base.into(), self.repacker);
            let output =
                self.insert_region_projection_node(output, capabilities.get(output.into()));
            output_nodes.insert(output);
        }

        for input in &input_nodes {
            for output in &output_nodes {
                self.edges.insert(GraphEdge::Abstract {
                    blocked: *input,
                    blocking: *output,
                });
            }
        }

        if abstraction.is_loop() {
            for output1 in output_nodes.iter() {
                for output2 in output_nodes.iter() {
                    if output1 < output2 {
                        self.edges.insert(GraphEdge::Coupled {
                            source: *output1,
                            target: *output2,
                        });
                    }
                }
            }
        }

        assert!(!input_nodes.is_empty());
        let cluster = GraphCluster {
            id: format!(
                "c{:?}_{}",
                abstraction.location().block,
                abstraction.location().statement_index
            ),
            label: format!("{:?}", abstraction.location()),
            nodes: input_nodes
                .iter()
                .chain(output_nodes.iter())
                .cloned()
                .collect(),
            min_rank_nodes: Some(input_nodes),
        };
        self.region_clusters.insert(cluster);
    }

    fn insert_remote_node(
        &mut self,
        remote_place: RemotePlace,
        capability: Option<CapabilityKind>,
    ) -> NodeId {
        if let Some(id) = self.remote_nodes.existing_id(&remote_place) {
            return id;
        }
        let id = self.remote_nodes.node_id(&remote_place);
        let node = GraphNode {
            id,
            node_type: NodeType::PlaceNode {
                owned: false,
                label: format!("Target of input {:?}", remote_place.assigned_local()),
                location: None,
                capability,
                ty: format!("{:?}", remote_place.ty(self.repacker)),
            },
        };
        self.insert_node(node);
        id
    }

    fn insert_place_node(
        &mut self,
        place: Place<'tcx>,
        location: Option<SnapshotLocation>,
        capability_getter: &impl CapabilityGetter<'tcx>,
    ) -> NodeId {
        if let Some(node_id) = self.place_nodes.existing_id(&(place, location)) {
            return node_id;
        }
        let capability = capability_getter.get(place.to_pcg_node(self.repacker));
        let id = self.place_node_id(place, location);
        let label = format!("{:?}", place.to_string(self.repacker));
        let place_ty = place.ty(self.repacker);
        let node_type = NodeType::PlaceNode {
            owned: place.is_owned(self.repacker),
            label,
            capability,
            location,
            ty: format!("{:?}", place_ty.ty),
        };
        let node = GraphNode { id, node_type };
        self.insert_node(node);
        id
    }
}

trait PlaceGrapher<'mir, 'tcx: 'mir> {
    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'mir;
    fn insert_maybe_old_place(&mut self, place: MaybeOldPlace<'tcx>) -> NodeId {
        let capability_getter = self.capability_getter();
        let constructor = self.constructor();
        constructor.insert_place_node(place.place(), place.location(), &capability_getter)
    }
    fn insert_maybe_remote_place(&mut self, place: MaybeRemotePlace<'tcx>) -> NodeId {
        let capability_getter = self.capability_getter();
        let capability = capability_getter.get(place.to_pcg_node(self.repacker()));
        let constructor = self.constructor();
        match place {
            MaybeRemotePlace::Local(place) => self.insert_maybe_old_place(place),
            MaybeRemotePlace::Remote(local) => constructor.insert_remote_node(local, capability),
        }
    }
    fn insert_pcg_node(&mut self, node: PCGNode<'tcx>) -> NodeId {
        let capabilities = self.capability_getter();
        let node_capability = capabilities.get(node);
        match node {
            PCGNode::Place(place) => self.insert_maybe_remote_place(place),
            PCGNode::RegionProjection(rp) => self
                .constructor()
                .insert_region_projection_node(rp, node_capability),
        }
    }

    fn insert_local_node(&mut self, node: LocalNode<'tcx>) -> NodeId {
        let capabilities = self.capability_getter();
        let node_capability = capabilities.get(node.into());
        match node {
            LocalNode::Place(place) => self.insert_maybe_old_place(place),
            LocalNode::RegionProjection(rp) => {
                let rp = rp.to_region_projection(self.repacker());
                self.constructor()
                    .insert_region_projection_node(rp, node_capability)
            }
        }
    }
    fn constructor(&mut self) -> &mut GraphConstructor<'mir, 'tcx>;
    fn repacker(&self) -> PlaceRepacker<'mir, 'tcx>;
    fn draw_borrow_pcg_edge(
        &mut self,
        edge: impl BorrowPCGEdgeLike<'tcx>,
        capabilities: &impl CapabilityGetter<'tcx>,
    ) {
        match edge.kind() {
            BorrowPCGEdgeKind::BorrowPCGExpansion(deref_expansion) => {
                let base_node = self.insert_local_node(deref_expansion.base());
                for place in deref_expansion.expansion(self.repacker()).unwrap() {
                    let expansion_node = self.insert_local_node(place);
                    self.constructor().edges.insert(GraphEdge::DerefExpansion {
                        source: base_node,
                        target: expansion_node,
                        path_conditions: format!("{}", edge.conditions()),
                    });
                    if deref_expansion.is_deref_of_borrow(self.repacker())
                        && let PCGNode::Place(base) = deref_expansion.base()
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
                let assigned_rp_pcg_node = assigned_region_projection.to_pcg_node(self.repacker());
                let assigned_rp_node = self.constructor().insert_region_projection_node(
                    assigned_region_projection,
                    capabilities.get(assigned_rp_pcg_node),
                );
                self.constructor().edges.insert(GraphEdge::Borrow {
                    borrowed_place,
                    assigned_region_projection: assigned_rp_node,
                    location: borrow.reserve_location(),
                    region: borrow.borrow_region().map(|r| format!("{:?}", r)),
                    path_conditions: format!("{}", edge.conditions()),
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
        }
    }
}

pub struct BorrowsGraphConstructor<'a, 'tcx> {
    borrows_graph: &'a BorrowsGraph<'tcx>,
    constructor: GraphConstructor<'a, 'tcx>,
    repacker: PlaceRepacker<'a, 'tcx>,
}

impl<'a, 'tcx> BorrowsGraphConstructor<'a, 'tcx> {
    pub fn new(borrows_graph: &'a BorrowsGraph<'tcx>, repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            borrows_graph,
            constructor: GraphConstructor::new(repacker),
            repacker,
        }
    }

    pub fn construct_graph(mut self) -> Graph {
        for edge in self.borrows_graph.edges() {
            self.draw_borrow_pcg_edge(edge, &NullCapabilityGetter);
        }
        self.constructor.into_graph()
    }
}

pub struct PCSGraphConstructor<'a, 'tcx> {
    summary: &'a CapabilitySummary<'tcx>,
    borrows_domain: &'a BorrowsState<'tcx>,
    constructor: GraphConstructor<'a, 'tcx>,
    repacker: PlaceRepacker<'a, 'tcx>,
}

trait CapabilityGetter<'tcx> {
    fn get(&self, node: PCGNode<'tcx>) -> Option<CapabilityKind>;
}

struct PCGCapabilityGetter<'a, 'tcx> {
    summary: &'a CapabilitySummary<'tcx>,
    borrows_domain: &'a BorrowsState<'tcx>,
}

impl<'tcx> CapabilityGetter<'tcx> for PCGCapabilityGetter<'_, 'tcx> {
    fn get(&self, node: PCGNode<'tcx>) -> Option<CapabilityKind> {
        if let Some(cap) = self.borrows_domain.get_capability(node) {
            return Some(cap);
        }
        let place = node.as_current_place()?;
        let alloc = self.summary.get(place.local)?;
        if let CapabilityLocal::Allocated(projections) = alloc {
            projections.get_capability(place)
        } else {
            None
        }
    }
}

struct NullCapabilityGetter;

impl<'tcx> CapabilityGetter<'tcx> for NullCapabilityGetter {
    fn get(&self, _: PCGNode<'tcx>) -> Option<CapabilityKind> {
        None
    }
}

impl<'a, 'tcx> PlaceGrapher<'a, 'tcx> for PCSGraphConstructor<'a, 'tcx> {
    fn repacker(&self) -> PlaceRepacker<'a, 'tcx> {
        self.repacker
    }

    fn insert_maybe_old_place(&mut self, place: MaybeOldPlace<'tcx>) -> NodeId {
        match place {
            MaybeOldPlace::Current { place } => {
                self.constructor
                    .insert_place_node(place, None, &self.capability_getter())
            }
            MaybeOldPlace::OldPlace(snapshot_place) => self.insert_snapshot_place(snapshot_place),
        }
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'a, 'tcx> {
        &mut self.constructor
    }

    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'a {
        PCGCapabilityGetter {
            summary: self.summary,
            borrows_domain: self.borrows_domain,
        }
    }
}

impl<'a, 'tcx> PlaceGrapher<'a, 'tcx> for BorrowsGraphConstructor<'a, 'tcx> {
    fn repacker(&self) -> PlaceRepacker<'a, 'tcx> {
        self.repacker
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'a, 'tcx> {
        &mut self.constructor
    }

    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'a {
        NullCapabilityGetter
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
        capabilities: &impl CapabilityGetter<'tcx>,
    ) -> NodeId {
        let node = self
            .constructor
            .insert_place_node(place, location, capabilities);
        if location.is_some() {
            return node;
        }
        let mut projection = place.projection;
        let mut last_node = node;
        let mut last_place = place.into();
        while !projection.is_empty() {
            projection = &projection[..projection.len() - 1];
            let place = Place::new(place.local, projection);
            let connections = RegionProjection::connections_between_places(
                place.into(),
                last_place,
                self.repacker,
            );
            for (rp1, rp2) in connections {
                let source = self.constructor.insert_region_projection_node(
                    rp1.to_region_projection(self.repacker()),
                    capabilities.get(rp1.to_pcg_node(self.repacker())),
                );
                let target = self.constructor.insert_region_projection_node(
                    rp2.to_region_projection(self.repacker()),
                    capabilities.get(rp2.to_pcg_node(self.repacker())),
                );
                self.constructor
                    .edges
                    .insert(GraphEdge::Projection { source, target });
            }
            last_place = place.into();
            let node = self
                .constructor
                .insert_place_node(place, None, capabilities);
            self.constructor.edges.insert(GraphEdge::Projection {
                source: node,
                target: last_node,
            });
            last_node = node;
        }
        node
    }

    fn insert_snapshot_place(&mut self, place: PlaceSnapshot<'tcx>) -> NodeId {
        let capability_getter = &PCGCapabilityGetter {
            summary: self.summary,
            borrows_domain: self.borrows_domain,
        };
        self.insert_place_and_previous_projections(place.place, Some(place.at), capability_getter)
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.constructor.repacker.tcx()
    }

    pub fn construct_graph(mut self) -> Graph {
        for capability in self.summary.iter() {
            match capability {
                CapabilityLocal::Unallocated => {}
                CapabilityLocal::Allocated(projections) => {
                    for place in projections.place_capabilities().keys() {
                        let capability_getter = &PCGCapabilityGetter {
                            summary: self.summary,
                            borrows_domain: self.borrows_domain,
                        };
                        self.insert_place_and_previous_projections(*place, None, capability_getter);
                    }
                }
            }
        }
        for edge in self.borrows_domain.graph_edges() {
            self.draw_borrow_pcg_edge(edge, &self.capability_getter());
        }

        self.constructor.into_graph()
    }
}
