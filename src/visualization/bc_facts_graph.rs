use petgraph::graph::NodeIndex;

use crate::rustc_interface::borrowck::PoloniusRegionVid;
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::mir::Location;
use crate::rustc_interface::middle::ty::RegionVid;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::CompilerCtxt;

use super::{
    dot_graph::{DotEdge, DotGraph, DotNode, EdgeDirection, EdgeOptions},
    node::IdLookup,
};

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for PoloniusRegionVid {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, '_>) -> String {
        let region: RegionVid = (*self).into();
        region.to_short_string(ctxt)
    }
}

fn get_id<'tcx, T: Clone + Eq + DisplayWithCompilerCtxt<'tcx>>(
    elem: &T,
    nodes: &mut IdLookup<T>,
    graph_nodes: &mut Vec<DotNode>,
    ctxt: CompilerCtxt<'_, 'tcx, '_>,
) -> String {
    if let Some(id) = nodes.existing_id(elem) {
        id.to_string()
    } else {
        let id = nodes.node_id(elem);
        graph_nodes.push(DotNode::simple(id.to_string(), elem.to_short_string(ctxt)));
        id.to_string()
    }
}

pub fn subset_anywhere(ctxt: CompilerCtxt<'_, '_, '_>) -> DotGraph {
    tracing::info!("Generating BC facts graph");
    let mut graph = DotGraph {
        nodes: vec![],
        edges: vec![],
        name: "bcfacts".to_string(),
    };
    let mut nodes = IdLookup::new('n');
    for loc in ctxt.bc.polonius_output().unwrap().subset.values() {
        for (sup, subs) in loc {
            let sup_node = get_id(sup, &mut nodes, &mut graph.nodes, ctxt);
            for sub in subs {
                let sub_node = get_id(sub, &mut nodes, &mut graph.nodes, ctxt);
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

pub fn region_inference_outlives(ctxt: CompilerCtxt<'_, '_, '_>) -> String {
    let mut graph = petgraph::Graph::new();
    let region_infer_ctxt = ctxt.bc.region_inference_ctxt();
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
                    .map(|r| r.to_short_string(ctxt))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        },
        |_, _| "",
    );
    petgraph::dot::Dot::new(&scc_graph).to_string()
}

pub fn subset_at_location(
    location: Location,
    start: bool,
    ctxt: CompilerCtxt<'_, '_, '_>,
) -> DotGraph {
    let mut graph = DotGraph {
        nodes: vec![],
        edges: vec![],
        name: "bcfacts".to_string(),
    };
    let mut nodes = IdLookup::new('n');
    let location_index = if start {
        ctxt.bc.location_table().start_index(location)
    } else {
        ctxt.bc.location_table().mid_index(location)
    };
    if let Some(subset) = ctxt
        .bc
        .polonius_output()
        .unwrap()
        .subset
        .get(&location_index)
    {
        for (sup, subs) in subset {
            let sup_node = get_id(sup, &mut nodes, &mut graph.nodes, ctxt);
            for sub in subs {
                let sub_node = get_id(sub, &mut nodes, &mut graph.nodes, ctxt);
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
