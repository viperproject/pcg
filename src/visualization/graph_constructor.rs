use crate::{
    borrow_pcg::{
        coupling_graph_constructor::CGNode,
        graph::{materialize::MaterializedEdge, BorrowsGraph},
        region_projection::RegionProjection,
        state::BorrowsState,
    },
    combined_pcs::MaybeHasLocation,
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityLocals},
    utils::{
        display::DisplayWithRepacker, HasPlace, Place, PlaceRepacker, PlaceSnapshot,
        SnapshotLocation,
    },
};

use super::{
    grapher::{CapabilityGetter, Grapher},
    node::IdLookup,
    Graph, GraphEdge, GraphNode, NodeId, NodeType,
};
use crate::borrow_pcg::edge::abstraction::AbstractionType;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::place::remote::RemotePlace;
use std::collections::{BTreeSet, HashSet};

pub(super) struct GraphConstructor<'mir, 'tcx> {
    remote_nodes: IdLookup<RemotePlace>,
    place_nodes: IdLookup<(Place<'tcx>, Option<SnapshotLocation>)>,
    region_projection_nodes: IdLookup<RegionProjection<'tcx>>,
    nodes: Vec<GraphNode>,
    pub(super) edges: HashSet<GraphEdge>,
    repacker: PlaceRepacker<'mir, 'tcx>,
}

impl<'a, 'tcx> GraphConstructor<'a, 'tcx> {
    fn new(repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            remote_nodes: IdLookup::new('a'),
            place_nodes: IdLookup::new('p'),
            region_projection_nodes: IdLookup::new('r'),
            nodes: vec![],
            edges: HashSet::new(),
            repacker,
        }
    }

    fn into_graph(self) -> Graph {
        Graph::new(self.nodes, self.edges)
    }

    fn place_node_id(&mut self, place: Place<'tcx>, location: Option<SnapshotLocation>) -> NodeId {
        self.place_nodes.node_id(&(place, location))
    }

    fn insert_node(&mut self, node: GraphNode) {
        if !self.nodes.contains(&node) {
            self.nodes.push(node);
        }
    }

    pub(super) fn insert_region_projection_node(
        &mut self,
        projection: RegionProjection<'tcx>,
    ) -> NodeId {
        if let Some(id) = self.region_projection_nodes.existing_id(&projection) {
            return id;
        }
        let id = self.region_projection_nodes.node_id(&projection);
        let node = GraphNode {
            id,
            node_type: NodeType::RegionProjectionNode {
                label: format!(
                    "{}↓{}",
                    projection.place().to_short_string(self.repacker),
                    projection.region(self.repacker),
                ),
            },
        };
        self.insert_node(node);
        id
    }

    pub(super) fn insert_cg_node(
        &mut self,
        node: CGNode<'tcx>,
        capability: &impl CapabilityGetter<'tcx>,
    ) -> NodeId {
        match node {
            CGNode::RegionProjection(rp) => self.insert_region_projection_node(rp.into()),
            CGNode::Place(MaybeRemotePlace::Local(place)) => {
                self.insert_place_node(place.place(), place.location(), capability)
            }
            CGNode::Place(MaybeRemotePlace::Remote(place)) => self.insert_remote_node(place),
        }
    }

    pub(super) fn insert_abstraction(
        &mut self,
        abstraction: &AbstractionType<'tcx>,
        capabilities: &impl CapabilityGetter<'tcx>,
    ) {
        let mut input_nodes = BTreeSet::new();
        let mut output_nodes = BTreeSet::new();

        for input in abstraction.inputs() {
            let input = self.insert_cg_node(input, capabilities);
            input_nodes.insert(input);
        }

        for output in abstraction.outputs() {
            let output = output.with_base(output.base.into(), self.repacker);
            let output = self.insert_region_projection_node(output);
            output_nodes.insert(output);
        }

        let label = match abstraction {
            AbstractionType::FunctionCall(fc) => {
                format!(
                    "call {} at {:?}",
                    self.repacker.tcx().def_path_str(fc.def_id()),
                    fc.location()
                )
            }
            AbstractionType::Loop(loop_abstraction) => {
                format!("loop at {:?}", loop_abstraction.location())
            }
        };

        for input in &input_nodes {
            for output in &output_nodes {
                self.edges.insert(GraphEdge::Abstract {
                    blocked: *input,
                    blocking: *output,
                    label: label.clone(),
                });
            }
        }
    }

    pub(super) fn insert_remote_node(&mut self, remote_place: RemotePlace) -> NodeId {
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
                capability: None,
                ty: format!("{:?}", remote_place.ty(self.repacker)),
            },
        };
        self.insert_node(node);
        id
    }

    pub(super) fn insert_place_node(
        &mut self,
        place: Place<'tcx>,
        location: Option<SnapshotLocation>,
        capability_getter: &impl CapabilityGetter<'tcx>,
    ) -> NodeId {
        if let Some(node_id) = self.place_nodes.existing_id(&(place, location)) {
            return node_id;
        }
        let capability = capability_getter.get(place.into());
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

pub struct BorrowsGraphConstructor<'graph, 'mir, 'tcx> {
    borrows_graph: &'graph BorrowsGraph<'tcx>,
    constructor: GraphConstructor<'mir, 'tcx>,
    repacker: PlaceRepacker<'mir, 'tcx>,
}

impl<'graph, 'mir: 'graph, 'tcx: 'mir> BorrowsGraphConstructor<'graph, 'mir, 'tcx> {
    pub fn new(
        borrows_graph: &'graph BorrowsGraph<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> Self {
        Self {
            borrows_graph,
            constructor: GraphConstructor::new(repacker),
            repacker,
        }
    }

    pub(crate) fn construct_graph(mut self) -> Graph {
        let edges: Vec<MaterializedEdge<'tcx, 'graph>> =
            self.borrows_graph.materialized_edges(self.repacker);
        for edge in edges {
            self.draw_materialized_edge(edge);
        }
        self.constructor.into_graph()
    }
}

pub(crate) struct PcgGraphConstructor<'a, 'tcx> {
    summary: &'a CapabilityLocals<'tcx>,
    borrows_domain: &'a BorrowsState<'tcx>,
    constructor: GraphConstructor<'a, 'tcx>,
    repacker: PlaceRepacker<'a, 'tcx>,
}

struct PCGCapabilityGetter<'a, 'tcx> {
    summary: &'a CapabilityLocals<'tcx>,
    borrows_domain: &'a BorrowsState<'tcx>,
}

impl<'tcx> CapabilityGetter<'tcx> for PCGCapabilityGetter<'_, 'tcx> {
    fn get(&self, node: MaybeOldPlace<'tcx>) -> Option<CapabilityKind> {
        if let Some(cap) = self.borrows_domain.get_capability(node) {
            return Some(cap);
        }
        let alloc = self.summary.get(node.place().local)?;
        if let CapabilityLocal::Allocated(projections) = alloc {
            projections.get_capability(node.place())
        } else {
            None
        }
    }
}

struct NullCapabilityGetter;

impl<'tcx> CapabilityGetter<'tcx> for NullCapabilityGetter {
    fn get(&self, _: MaybeOldPlace<'tcx>) -> Option<CapabilityKind> {
        None
    }
}

impl<'a, 'tcx> Grapher<'a, 'tcx> for PcgGraphConstructor<'a, 'tcx> {
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

impl<'graph, 'mir: 'graph, 'tcx: 'graph> Grapher<'mir, 'tcx>
    for BorrowsGraphConstructor<'graph, 'mir, 'tcx>
{
    fn repacker(&self) -> PlaceRepacker<'mir, 'tcx> {
        self.repacker
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'mir, 'tcx> {
        &mut self.constructor
    }

    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'mir {
        NullCapabilityGetter
    }
}

impl<'a, 'tcx> PcgGraphConstructor<'a, 'tcx> {
    pub fn new(
        summary: &'a CapabilityLocals<'tcx>,
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
        while !projection.is_empty() {
            projection = &projection[..projection.len() - 1];
            let place = Place::new(place.local, projection);
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

    pub fn construct_graph(mut self) -> Graph {
        let capability_getter = &PCGCapabilityGetter {
            summary: self.summary,
            borrows_domain: self.borrows_domain,
        };
        for (local, capability) in self.summary.iter_enumerated() {
            match capability {
                CapabilityLocal::Unallocated => {}
                CapabilityLocal::Allocated(projections) => {
                    self.insert_place_and_previous_projections(
                        local.into(),
                        None,
                        capability_getter,
                    );
                    for (place, expansion) in projections.expansions() {
                        self.insert_place_and_previous_projections(*place, None, capability_getter);
                        for child_place in place.expansion_places(expansion, self.repacker) {
                            self.insert_place_and_previous_projections(
                                child_place,
                                None,
                                capability_getter,
                            );
                        }
                    }
                }
            }
        }
        for edge in self
            .borrows_domain
            .graph()
            .materialized_edges(self.repacker)
        {
            self.draw_materialized_edge(edge);
        }

        self.constructor.into_graph()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        run_pcg, utils::PlaceRepacker,
        visualization::graph_constructor::PcgGraphConstructor,
    };

    // 26_ref_in_struct.rs
    #[test]
    fn test_expand_created() {
        let input = r#"
        struct S<'a> {
    x: &'a mut i32,
    y: &'a mut i32,
}

fn main() {
    let mut x = 1;
    let mut y = 2;
    let s = S { x: &mut x, y: &mut y };
    let rx = s.x;
    *rx = 1;
}
"#;
        rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
            let repacker = PlaceRepacker::new(&body.body, tcx);
            let mut pcg = run_pcg(body, tcx, None);
            let bb = pcg.get_all_for_bb(0usize.into()).unwrap().unwrap();
            let stmt = &bb.statements[22];
            let graph =
                PcgGraphConstructor::new(&stmt.states.post_main, repacker, &stmt.borrows.post_main)
                    .construct_graph();
            if let Err(e) = graph.edge_between_labelled_nodes("_3 = s", "_3.0 = s.x") {
                panic!("{}", e);
            }
        });
    }
}
