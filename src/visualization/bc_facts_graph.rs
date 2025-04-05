use crate::borrow_pcg::region_projection::display_region_vid;
use petgraph::graph::NodeIndex;

use crate::rustc_interface::borrowck::PoloniusOutput;
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::mir::Location;
use crate::rustc_interface::middle::ty::RegionVid;
use crate::BodyAndBorrows;

use super::{
    dot_graph::{DotEdge, DotGraph, DotNode, EdgeDirection, EdgeOptions},
    node::IdLookup,
};

fn get_id<T: Clone + Eq + std::fmt::Debug>(
    constraint: &T,
    nodes: &mut IdLookup<T>,
    graph_nodes: &mut Vec<DotNode>,
) -> String {
    if let Some(id) = nodes.existing_id(constraint) {
        id.to_string()
    } else {
        let id = nodes.node_id(constraint);
        graph_nodes.push(DotNode::simple(id.to_string(), format!("{:?}", constraint)));
        id.to_string()
    }
}

pub fn subset_anywhere(output_facts: &PoloniusOutput) -> DotGraph {
    tracing::info!("Generating BC facts graph");
    let mut graph = DotGraph {
        nodes: vec![],
        edges: vec![],
        name: "bcfacts".to_string(),
    };
    let mut nodes = IdLookup::new('n');
    for loc in output_facts.subset.values() {
        for (sup, subs) in loc {
            let sup_node = get_id(sup, &mut nodes, &mut graph.nodes);
            for sub in subs {
                let sub_node = get_id(sub, &mut nodes, &mut graph.nodes);
                let edge = DotEdge {
                    from: sup_node.to_string(),
                    to: sub_node.to_string(),
                    options: EdgeOptions::directed(EdgeDirection::Forward),
                };
                if !graph.edges.contains(&edge) {
                    graph.edges.push(edge);
                }
            }
        }
    }
    graph
}

pub fn region_inference_outlives<'tcx>(body: &impl BodyAndBorrows<'tcx>) -> String {
    let mut graph = petgraph::Graph::new();
    let region_infer_ctxt = body.region_inference_context();
    let regions = region_infer_ctxt
        .var_infos
        .iter_enumerated()
        .map(|(r, _)| r)
        .collect::<Vec<_>>();
    let indices: IndexVec<RegionVid, NodeIndex> = regions
        .iter()
        .copied()
        .map(|r| graph.add_node(r))
        .collect::<IndexVec<_, _>>();
    for r1 in regions.iter() {
        for r2 in regions.iter() {
            if r1 != r2 && region_infer_ctxt.eval_outlives(*r1, *r2) {
                graph.add_edge(indices[*r1], indices[*r2], ());
            }
        }
    }
    let mut scc_graph = petgraph::algo::condensation(graph, true);
    let toposort = petgraph::algo::toposort(&scc_graph, None).unwrap();
    let (g, revmap) = petgraph::algo::tred::dag_to_toposorted_adjacency_list(&scc_graph, &toposort);
    let (reduced, _) = petgraph::algo::tred::dag_transitive_reduction_closure::<_, u32>(&g);
    scc_graph.retain_edges(|slf, ei| {
        let endpoints = slf.edge_endpoints(ei).unwrap();
        reduced.contains_edge(revmap[endpoints.0.index()], revmap[endpoints.1.index()])
    });
    let scc_graph = scc_graph.map(
        |_, regions| {
            format!(
                "[{}]",
                regions
                .iter()
                    .map(|r| display_region_vid(*r, region_infer_ctxt))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        },
        |_, _| "",
    );
    petgraph::dot::Dot::new(&scc_graph).to_string()
}

pub fn subset_at_location<'tcx>(
    body: &impl BodyAndBorrows<'tcx>,
    output_facts: &PoloniusOutput,
    location: Location,
    start: bool,
) -> DotGraph {
    let mut graph = DotGraph {
        nodes: vec![],
        edges: vec![],
        name: "bcfacts".to_string(),
    };
    let mut nodes = IdLookup::new('n');
    let location_index = if start {
        body.location_table().start_index(location)
    } else {
        body.location_table().mid_index(location)
    };
    if let Some(subset) = output_facts.subset.get(&location_index) {
        for (sup, subs) in subset {
            let sup_node = get_id(sup, &mut nodes, &mut graph.nodes);
            for sub in subs {
                let sub_node = get_id(sub, &mut nodes, &mut graph.nodes);
                graph.edges.push(DotEdge {
                    from: sup_node.to_string(),
                    to: sub_node.to_string(),
                    options: EdgeOptions::directed(EdgeDirection::Forward),
                });
            }
        }
    } else {
        tracing::warn!("No subset found for location {:?}", location);
    }
    graph
}
