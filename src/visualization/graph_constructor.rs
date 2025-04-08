use crate::{
    borrow_pcg::{
        coupling_graph_constructor::CGNode,
        graph::{materialize::MaterializedEdge, BorrowsGraph},
        region_projection::{MaybeRemoteRegionProjectionBase, RegionProjection},
        state::BorrowsState,
    },
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityLocals},
    pcg::{place_capabilities::PlaceCapabilities, MaybeHasLocation},
    rustc_interface::borrowck::BorrowIndex,
    rustc_interface::middle::mir,
    utils::{
        display::DisplayWithCompilerCtxt, CompilerCtxt, HasPlace, Place, PlaceSnapshot,
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

pub(super) struct GraphConstructor<'mir, 'tcx, 'bc> {
    remote_nodes: IdLookup<RemotePlace>,
    place_nodes: IdLookup<(Place<'tcx>, Option<SnapshotLocation>)>,
    region_projection_nodes: IdLookup<RegionProjection<'tcx>>,
    nodes: Vec<GraphNode>,
    pub(super) edges: HashSet<GraphEdge>,
    ctxt: CompilerCtxt<'mir, 'tcx, 'bc>,
    location: mir::Location,
}

impl<'a, 'tcx, 'bc> GraphConstructor<'a, 'tcx, 'bc> {
    fn new(repacker: CompilerCtxt<'a, 'tcx, 'bc>, location: mir::Location) -> Self {
        Self {
            remote_nodes: IdLookup::new('a'),
            place_nodes: IdLookup::new('p'),
            region_projection_nodes: IdLookup::new('r'),
            nodes: vec![],
            edges: HashSet::new(),
            ctxt: repacker,
            location,
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
            #[rustversion::since(2024-12-14)]
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
            #[rustversion::before(2024-12-14)]
            let render_loans = |loans: Option<&BTreeSet<BorrowIndex>>| {
                if let Some(loans) = loans {
                    format!(
                        "{{{}}}",
                        loans
                            .iter()
                            .map(|l| format!("{:?}", self.ctxt.bc.borrow_index_to_region(*l)))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    "{}".to_string()
                }
            };
            let loans_before = render_loans(
                output
                    .origin_contains_loan_at(
                        self.ctxt.bc.location_table().start_index(self.location),
                    )
                    .get(&region_vid),
            );
            let loans_after = render_loans(
                output
                    .origin_contains_loan_at(self.ctxt.bc.location_table().mid_index(self.location))
                    .get(&region_vid),
            );
            format!(
                "Loans in {:?} - before: {}, mid: {}",
                projection.region(self.ctxt),
                loans_before,
                loans_after
            )
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
        edge_idx: usize,
    ) {
        let mut input_nodes = BTreeSet::new();
        let mut output_nodes = BTreeSet::new();

        for input in abstraction.inputs() {
            let input = self.insert_cg_node(input, capabilities);
            input_nodes.insert(input);
        }

        for output in abstraction.outputs() {
            let output = output.with_base(output.base.into(), self.ctxt);
            let output = self.insert_region_projection_node(output);
            output_nodes.insert(output);
        }

        let label = match abstraction {
            AbstractionType::FunctionCall(fc) => {
                format!(
                    "call {} at {:?}",
                    self.ctxt.tcx().def_path_str(fc.def_id()),
                    fc.location()
                )
            }
            AbstractionType::Loop(loop_abstraction) => {
                format!("loop at {:?}", loop_abstraction.location())
            }
        };

        let label = if input_nodes.len() > 1 || output_nodes.len() > 1 {
            format!("{label} <{}>", edge_idx)
        } else {
            label
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
        let capability = capability_getter.get(place.into());
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
        id
    }
}

pub struct BorrowsGraphConstructor<'graph, 'mir, 'tcx, 'bc> {
    borrows_graph: &'graph BorrowsGraph<'tcx>,
    constructor: GraphConstructor<'mir, 'tcx, 'bc>,
    repacker: CompilerCtxt<'mir, 'tcx, 'bc>,
}

impl<'graph, 'mir: 'graph, 'tcx: 'mir, 'bc: 'graph>
    BorrowsGraphConstructor<'graph, 'mir, 'tcx, 'bc>
{
    pub fn new(
        borrows_graph: &'graph BorrowsGraph<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx, 'bc>,
        location: mir::Location,
    ) -> Self {
        Self {
            borrows_graph,
            constructor: GraphConstructor::new(ctxt, location),
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

pub(crate) struct PcgGraphConstructor<'pcg, 'a, 'tcx, 'bc> {
    summary: &'pcg CapabilityLocals<'tcx>,
    borrows_domain: &'pcg BorrowsState<'tcx>,
    capabilities: &'pcg PlaceCapabilities<'tcx>,
    constructor: GraphConstructor<'a, 'tcx, 'bc>,
    repacker: CompilerCtxt<'a, 'tcx, 'bc>,
}

struct PCGCapabilityGetter<'a, 'tcx> {
    capabilities: &'a PlaceCapabilities<'tcx>,
}

impl<'tcx> CapabilityGetter<'tcx> for PCGCapabilityGetter<'_, 'tcx> {
    fn get(&self, place: MaybeOldPlace<'tcx>) -> Option<CapabilityKind> {
        self.capabilities.get(place)
    }
}

struct NullCapabilityGetter;

impl<'tcx> CapabilityGetter<'tcx> for NullCapabilityGetter {
    fn get(&self, _: MaybeOldPlace<'tcx>) -> Option<CapabilityKind> {
        None
    }
}

impl<'pcg, 'a, 'tcx, 'bc> Grapher<'pcg, 'a, 'tcx, 'bc>
    for PcgGraphConstructor<'pcg, 'a, 'tcx, 'bc>
{
    fn repacker(&self) -> CompilerCtxt<'a, 'tcx, 'bc> {
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

    fn constructor(&mut self) -> &mut GraphConstructor<'a, 'tcx, 'bc> {
        &mut self.constructor
    }

    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'pcg {
        PCGCapabilityGetter {
            capabilities: self.capabilities,
        }
    }
}

impl<'graph, 'mir: 'graph, 'tcx: 'graph, 'bc> Grapher<'graph, 'mir, 'tcx, 'bc>
    for BorrowsGraphConstructor<'graph, 'mir, 'tcx, 'bc>
{
    fn repacker(&self) -> CompilerCtxt<'mir, 'tcx, 'bc> {
        self.repacker
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'mir, 'tcx, 'bc> {
        &mut self.constructor
    }

    fn capability_getter(&self) -> impl CapabilityGetter<'tcx> + 'graph {
        NullCapabilityGetter
    }
}

impl<'pcg, 'a, 'tcx, 'bc> PcgGraphConstructor<'pcg, 'a, 'tcx, 'bc> {
    pub fn new(
        summary: &'pcg CapabilityLocals<'tcx>,
        repacker: CompilerCtxt<'a, 'tcx, 'bc>,
        borrows_domain: &'pcg BorrowsState<'tcx>,
        capabilities: &'pcg PlaceCapabilities<'tcx>,
        location: mir::Location,
    ) -> Self {
        Self {
            summary,
            borrows_domain,
            capabilities,
            constructor: GraphConstructor::new(repacker, location),
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
            capabilities: self.capabilities,
        };
        self.insert_place_and_previous_projections(place.place, Some(place.at), capability_getter)
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
            .graph()
            .materialized_edges(self.repacker)
            .into_iter()
            .enumerate()
        {
            self.draw_materialized_edge(edge, edge_idx);
        }

        self.constructor.into_graph()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        borrow_pcg::borrow_checker::r#impl::BorrowCheckerImpl, run_pcg, utils::CompilerCtxt,
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
            let bc = BorrowCheckerImpl::new(tcx, body);
            let ctxt: CompilerCtxt<'_, '_, '_> = CompilerCtxt::new(&body.body, tcx, &bc);
            let mut pcg = run_pcg(&body.body, tcx, &bc, None);
            let bb = pcg.get_all_for_bb(0usize.into()).unwrap().unwrap();
            let stmt = &bb.statements[22];
            let pcg = &stmt.states.0.post_main;
            let graph = PcgGraphConstructor::new(
                &pcg.owned.locals(),
                ctxt,
                &pcg.borrow,
                &pcg.capabilities,
                stmt.location,
            )
            .construct_graph();
            if let Err(e) = graph.edge_between_labelled_nodes("_3 = s", "_3.0 = s.x") {
                panic!("{}", e);
            }
        });
    }
}
