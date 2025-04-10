use std::collections::{BTreeMap, BTreeSet};

use petgraph::graph::NodeIndex;

use crate::borrow_pcg::coupling_graph_constructor::BorrowCheckerInterface;
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::mir::Location;
use crate::rustc_interface::middle::ty::RegionVid;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::CompilerCtxt;
use crate::{
    borrow_pcg::borrow_checker::r#impl::PoloniusBorrowChecker,
    rustc_interface::borrowck::{PoloniusRegionVid, RegionInferenceContext},
};

use super::{
    dot_graph::{DotEdge, DotGraph, DotNode, EdgeDirection, EdgeOptions},
    node::IdLookup,
};

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for PoloniusRegionVid {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        let region: RegionVid = (*self).into();
        region.to_short_string(ctxt)
    }
}

fn get_id<
    'a,
    'tcx: 'a,
    'bc,
    T: Clone + Eq + DisplayWithCompilerCtxt<'tcx>,
    BC: BorrowCheckerInterface<'tcx> + ?Sized,
>(
    elem: &T,
    nodes: &mut IdLookup<T>,
    graph_nodes: &mut Vec<DotNode>,
    ctxt: CompilerCtxt<'a, 'tcx, &'bc BC>,
) -> String {
    if let Some(id) = nodes.existing_id(elem) {
        id.to_string()
    } else {
        let id = nodes.node_id(elem);
        graph_nodes.push(DotNode::simple(
            id.to_string(),
            elem.to_short_string(ctxt.as_dyn()),
        ));
        id.to_string()
    }
}

pub fn subset_anywhere<'a, 'tcx: 'a, 'bc>(
    ctxt: CompilerCtxt<'a, 'tcx, &'bc PoloniusBorrowChecker<'a, 'tcx>>,
) -> DotGraph {
    tracing::info!("Generating BC facts graph");
    let mut graph = DotGraph {
        nodes: vec![],
        edges: vec![],
        name: "bcfacts".to_string(),
    };
    let mut nodes = IdLookup::new('n');
    for loc in ctxt.bc.output_facts.subset.values() {
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

#[derive(Clone)]
pub(crate) struct RegionPrettyPrinter {
    sccs: Vec<BTreeSet<RegionVid>>,
    region_to_string: BTreeMap<usize, String>,
}

impl RegionPrettyPrinter {
    pub(crate) fn new(region_infer_ctxt: &RegionInferenceContext<'_>) -> Self {
        let scc_graph = compute_region_sccs(region_infer_ctxt);
        let sccs = scc_graph
            .node_weights()
            .into_iter()
            .map(|r| r.clone().into_iter().collect())
            .collect();
        RegionPrettyPrinter {
            sccs,
            region_to_string: BTreeMap::new(),
        }
    }

    fn index(&self, region: RegionVid) -> usize {
        self.sccs
            .iter()
            .position(|scc| scc.contains(&region))
            .unwrap()
    }

    pub(crate) fn insert(&mut self, region: RegionVid, string: String) {
        let scc = self.index(region);
        assert!(self.region_to_string.insert(scc, string).is_none());
    }

    pub(crate) fn lookup(&self, region: RegionVid) -> Option<&String> {
        self.region_to_string.get(&self.index(region))
    }
}

fn compute_region_sccs(
    region_infer_ctxt: &RegionInferenceContext<'_>,
) -> petgraph::Graph<Vec<RegionVid>, ()> {
    let mut graph = petgraph::Graph::new();
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
    scc_graph
}
pub fn region_inference_outlives<'a, 'tcx: 'a, 'bc, T: BorrowCheckerInterface<'tcx> + ?Sized>(
    ctxt: CompilerCtxt<'a, 'tcx, &'bc T>,
) -> String {
    let scc_graph = compute_region_sccs(ctxt.bc.region_inference_ctxt());
    let scc_graph = scc_graph.map(
        |_, regions| {
            format!(
                "[{}]",
                regions
                    .iter()
                    .map(|r| r.to_short_string(ctxt.as_dyn()))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        },
        |_, _| "",
    );
    petgraph::dot::Dot::new(&scc_graph).to_string()
}

pub fn subset_at_location<'a, 'tcx: 'a, 'bc>(
    location: Location,
    start: bool,
    ctxt: CompilerCtxt<'a, 'tcx, &'bc PoloniusBorrowChecker<'a, 'tcx>>,
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
    if let Some(subset) = ctxt.bc.output_facts.subset.get(&location_index) {
        for (sup, subs) in subset {
            let sup_node = get_id(sup, &mut nodes, &mut graph.nodes, ctxt.as_dyn());
            for sub in subs {
                let sub_node = get_id(sub, &mut nodes, &mut graph.nodes, ctxt);
                graph.edges.push(DotEdge {
                    from: sup_node.to_string(),
                    to: sub_node.to_string(),
                    options: EdgeOptions::directed(EdgeDirection::Forward),
                });
            }
        }
    }
    graph
}
