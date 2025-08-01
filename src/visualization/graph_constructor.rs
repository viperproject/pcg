use crate::{
    borrow_pcg::{
        graph::{BorrowsGraph, materialize::MaterializedEdge},
        region_projection::{MaybeRemoteRegionProjectionBase, RegionProjection},
        state::BorrowStateRef,
    },
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityLocals},
    pcg::{
        MaybeHasLocation, PCGNode, PcgRef,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    rustc_interface::{borrowck::BorrowIndex, middle::mir},
    utils::{CompilerCtxt, HasPlace, Place, SnapshotLocation, display::DisplayWithCompilerCtxt},
};

use super::{
    Graph, GraphEdge, GraphNode, NodeId, NodeType,
    grapher::{CapabilityGetter, Grapher},
    node::IdLookup,
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
    ctxt: CompilerCtxt<'mir, 'tcx>,
    location: Option<mir::Location>,
}

impl<'a, 'tcx> GraphConstructor<'a, 'tcx> {
    fn new(ctxt: CompilerCtxt<'a, 'tcx>, location: Option<mir::Location>) -> Self {
        Self {
            remote_nodes: IdLookup::new('a'),
            place_nodes: IdLookup::new('p'),
            region_projection_nodes: IdLookup::new('r'),
            nodes: vec![],
            edges: HashSet::new(),
            ctxt,
            location,
        }
    }

    fn insert_maybe_old_place(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        capability_getter: &impl CapabilityGetter<'tcx>,
    ) -> NodeId {
        self.insert_place_node(place.place(), place.location(), capability_getter)
    }

    fn insert_maybe_remote_place(
        &mut self,
        place: MaybeRemotePlace<'tcx>,
        capability_getter: &impl CapabilityGetter<'tcx>,
    ) -> NodeId {
        match place {
            MaybeRemotePlace::Local(place) => self.insert_maybe_old_place(place, capability_getter),
            MaybeRemotePlace::Remote(local) => self.insert_remote_node(local),
        }
    }
    fn insert_pcg_node(
        &mut self,
        node: PCGNode<'tcx>,
        capability_getter: &impl CapabilityGetter<'tcx>,
    ) -> NodeId {
        match node {
            PCGNode::Place(place) => self.insert_maybe_remote_place(place, capability_getter),
            PCGNode::RegionProjection(rp) => self.insert_region_projection_node(rp),
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
        let base_ty = match projection.place() {
            MaybeRemoteRegionProjectionBase::Place(p) => {
                format!("{:?}", p.related_local_place().ty(self.ctxt).ty)
            }
            MaybeRemoteRegionProjectionBase::Const(c) => {
                format!("{:?}", c.ty())
            }
        };
        let loans = if let Some(output) = self.ctxt.bc.polonius_output()
            && let Some(region_vid) = projection.region(self.ctxt).vid()
        {
            let region_vid = region_vid.into();
            let render_loans = |loans: Option<&BTreeSet<BorrowIndex>>| {
                if let Some(loans) = loans {
                    format!(
                        "{{{}}}",
                        loans
                            .iter()
                            .map(|l| format!("{:?}", self.ctxt.bc.borrow_set()[*l].region()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    "{}".to_string()
                }
            };
            if let Some(location) = self.location {
                let location_table = self.ctxt.bc.rust_borrow_checker().unwrap().location_table();
                let loans_before = render_loans(
                    output
                        .origin_contains_loan_at(
                            location_table.start_index(location),
                        )
                        .get(&region_vid),
                );
                let loans_after = render_loans(
                    output
                        .origin_contains_loan_at(location_table.mid_index(location))
                        .get(&region_vid),
                );
                format!(
                    "Loans in {} - before: {}, mid: {}",
                    projection.region(self.ctxt).to_short_string(self.ctxt),
                    loans_before,
                    loans_after
                )
            } else {
                "".to_string()
            }
        } else {
            "".to_string()
        };
        let node = GraphNode {
            id,
            node_type: NodeType::RegionProjectionNode {
                label: projection.to_short_string(self.ctxt),
                base_ty,
                loans,
            },
        };
        self.insert_node(node);
        id
    }

    pub(super) fn insert_abstraction(
        &mut self,
        abstraction: &AbstractionType<'tcx>,
        capabilities: &impl CapabilityGetter<'tcx>,
        edge_idx: usize,
    ) {
        let mut input_nodes = vec![];
        let mut output_nodes = vec![];

        for input in abstraction.inputs() {
            let input = self.insert_pcg_node(*input, capabilities);
            input_nodes.push(input);
        }

        for output in abstraction.outputs() {
            let output = self.insert_pcg_node((*output).into(), capabilities);
            output_nodes.push(output);
        }

        let label = match abstraction {
            AbstractionType::FunctionCall(fc) => fc.to_short_string(self.ctxt),
            AbstractionType::Loop(loop_abstraction) => {
                format!("loop at {:?}", loop_abstraction.location())
            }
        };

        let use_label = input_nodes.len() > 1 || output_nodes.len() > 1;

        let hyperedge_id = format!("<{edge_idx}>");

        let first_edge_label = if use_label {
            format!("{label} {hyperedge_id}")
        } else {
            label
        };

        let mut first = true;

        // for i in 0..input_nodes.len() - 1{
        //     self.edges.insert(GraphEdge::HyperedgeSameEndpoint {
        //         source: input_nodes[i],
        //         target: input_nodes[i + 1],
        //         label: hyperedge_id.clone(),
        //     });
        // }
        // for i in 0..output_nodes.len() - 1 {
        //     self.edges.insert(GraphEdge::HyperedgeSameEndpoint {
        //         source: output_nodes[i],
        //         target: output_nodes[i + 1],
        //         label: hyperedge_id.clone(),
        //     });
        // }

        for input in &input_nodes {
            for output in &output_nodes {
                self.edges.insert(GraphEdge::Abstract {
                    blocked: *input,
                    blocking: *output,
                    label: if first {
                        first_edge_label.clone()
                    } else {
                        hyperedge_id.clone()
                    },
                });
                first = false
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
                ty: format!("{:?}", remote_place.ty(self.ctxt)),
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
        let capability = capability_getter.get(place);
        let id = self.place_node_id(place, location);
        let label = format!("{:?}", place.to_string(self.ctxt));
        let place_ty = place.ty(self.ctxt);
        let node_type = NodeType::PlaceNode {
            owned: place.is_owned(self.ctxt),
            label,
            capability,
            location,
            ty: format!("{:?}", place_ty.ty),
        };
        let node = GraphNode { id, node_type };
        self.insert_node(node);
        if matches!(
            capability,
            Some(CapabilityKind::Read | CapabilityKind::Exclusive)
        ) {
            for rp in place.region_projections(self.ctxt) {
                self.insert_region_projection_node(rp.into());
            }
        }
        id
    }
}

pub struct BorrowsGraphConstructor<'graph, 'mir, 'tcx> {
    borrows_graph: &'graph BorrowsGraph<'tcx>,
    constructor: GraphConstructor<'mir, 'tcx>,
    repacker: CompilerCtxt<'mir, 'tcx>,
}

impl<'graph, 'mir: 'graph, 'tcx: 'mir> BorrowsGraphConstructor<'graph, 'mir, 'tcx> {
    pub fn new(borrows_graph: &'graph BorrowsGraph<'tcx>, ctxt: CompilerCtxt<'mir, 'tcx>) -> Self {
        Self {
            borrows_graph,
            constructor: GraphConstructor::new(ctxt, None),
            repacker: ctxt,
        }
    }

    pub(crate) fn construct_graph(mut self) -> Graph {
        let edges: Vec<MaterializedEdge<'tcx, 'graph>> =
            self.borrows_graph.materialized_edges(self.repacker);
        for (edge_idx, edge) in edges.into_iter().enumerate() {
            self.draw_materialized_edge(edge, edge_idx);
        }
        self.constructor.into_graph()
    }
}

pub(crate) struct PcgGraphConstructor<'pcg, 'a, 'tcx> {
    summary: &'pcg CapabilityLocals<'tcx>,
    borrows_domain: BorrowStateRef<'pcg, 'tcx>,
    capabilities: &'pcg PlaceCapabilities<'tcx>,
    constructor: GraphConstructor<'a, 'tcx>,
    repacker: CompilerCtxt<'a, 'tcx>,
}

struct PCGCapabilityGetter<'a, 'tcx> {
    capabilities: &'a PlaceCapabilities<'tcx>,
}

impl<'tcx> CapabilityGetter<'tcx> for PCGCapabilityGetter<'_, 'tcx> {
    fn get(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        self.capabilities.get(place)
    }
}

struct NullCapabilityGetter;

impl<'tcx> CapabilityGetter<'tcx> for NullCapabilityGetter {
    fn get(&self, _: Place<'tcx>) -> Option<CapabilityKind> {
        None
    }
}

impl<'pcg, 'a: 'pcg, 'tcx> Grapher<'pcg, 'a, 'tcx> for PcgGraphConstructor<'pcg, 'a, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx> {
        self.repacker
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'a, 'tcx> {
        &mut self.constructor
    }

    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'pcg {
        PCGCapabilityGetter {
            capabilities: self.capabilities,
        }
    }
}

impl<'graph, 'mir: 'graph, 'tcx: 'mir> Grapher<'graph, 'mir, 'tcx>
    for BorrowsGraphConstructor<'graph, 'mir, 'tcx>
{
    fn ctxt(&self) -> CompilerCtxt<'mir, 'tcx> {
        self.repacker
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'mir, 'tcx> {
        &mut self.constructor
    }

    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'graph {
        NullCapabilityGetter
    }
}

impl<'pcg, 'a: 'pcg, 'tcx> PcgGraphConstructor<'pcg, 'a, 'tcx> {
    pub fn new(
        pcg: PcgRef<'pcg, 'tcx>,
        repacker: CompilerCtxt<'a, 'tcx>,
        location: mir::Location,
    ) -> Self {
        Self {
            summary: pcg.owned.locals(),
            borrows_domain: pcg.borrow,
            capabilities: pcg.capabilities,
            constructor: GraphConstructor::new(repacker, Some(location)),
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

    pub fn construct_graph(mut self) -> Graph {
        let capability_getter = &PCGCapabilityGetter {
            capabilities: self.capabilities,
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
        for (edge_idx, edge) in self
            .borrows_domain
            .graph
            .materialized_edges(self.repacker)
            .into_iter()
            .enumerate()
        {
            self.draw_materialized_edge(edge, edge_idx);
        }

        self.constructor.into_graph()
    }
}

#[rustversion::since(2025-05-24)]
#[cfg(test)]
mod tests {
    use crate::{
        utils::test::run_pcg_on_str, visualization::graph_constructor::PcgGraphConstructor,
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
        run_pcg_on_str(input, |mut analysis| {
            let bb = analysis.get_all_for_bb(0usize.into()).unwrap().unwrap();
            let ctxt = analysis.ctxt();
            let stmt = &bb.statements[22];
            let pcg = &stmt.states.0.post_main;
            let graph = PcgGraphConstructor::new(pcg.into(), ctxt, stmt.location).construct_graph();
            if let Err(e) = graph.edge_between_labelled_nodes("_3 = s", "_3.0 = s.x") {
                panic!("{}", e);
            }
        });
    }
}
