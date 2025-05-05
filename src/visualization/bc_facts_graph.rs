use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use itertools::Itertools;
use petgraph::graph::NodeIndex;

use crate::borrow_pcg::coupling_graph_constructor::BorrowCheckerInterface;
use crate::borrow_pcg::visitor::extract_regions;
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::mir::{Body, Location};
use crate::rustc_interface::middle::ty::{self, RegionVid};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::CompilerCtxt;
use crate::{
    borrow_checker::r#impl::PoloniusBorrowChecker,
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
pub(crate) struct RegionPrettyPrinter<'bc, 'tcx> {
    region_to_string: BTreeMap<RegionVid, String>,
    sccs: RefCell<Option<petgraph::Graph<Vec<RegionVid>, ()>>>,
    region_infer_ctxt: &'bc RegionInferenceContext<'tcx>,
}

impl<'bc, 'tcx> RegionPrettyPrinter<'bc, 'tcx> {
    pub(crate) fn new(region_infer_ctxt: &'bc RegionInferenceContext<'tcx>) -> Self {
        RegionPrettyPrinter {
            region_to_string: BTreeMap::new(),
            sccs: RefCell::new(None),
            region_infer_ctxt,
        }
    }

    pub(crate) fn insert(&mut self, region: RegionVid, string: String) {
        assert!(self.region_to_string.insert(region, string).is_none());
        self.sccs.borrow_mut().take();
    }

    pub(crate) fn lookup(&self, region: RegionVid) -> Option<&String> {
        if self.sccs.borrow().is_none() {
            let regions = self.region_to_string.keys().cloned().collect();
            *self.sccs.borrow_mut() = Some(compute_region_sccs(regions, self.region_infer_ctxt));
        }
        for scc in self.sccs.borrow().as_ref().unwrap().node_weights() {
            if scc.contains(&region) {
                for r in scc {
                    if let Some(s) = self.region_to_string.get(r) {
                        return Some(s);
                    }
                }
            }
        }
        None
    }
}

fn get_all_regions<'tcx, 'bc>(body: &Body<'tcx>, tcx: ty::TyCtxt<'tcx>) -> Vec<RegionVid> {
    body.local_decls
        .iter()
        .flat_map(|l| extract_regions(l.ty, CompilerCtxt::new(body, tcx, ())))
        .flat_map(|r| r.vid())
        .unique()
        .collect()
}

fn compute_region_sccs<'tcx, 'bc>(
    regions: Vec<RegionVid>,
    region_infer_ctxt: &RegionInferenceContext<'tcx>,
) -> petgraph::Graph<Vec<RegionVid>, ()> {
    let mut graph = petgraph::Graph::new();
    let indices: BTreeMap<RegionVid, NodeIndex> = regions
        .iter()
        .copied()
        .map(|r| (r, graph.add_node(r)))
        .collect::<BTreeMap<_, _>>();
    for r1 in regions.iter() {
        for r2 in regions.iter() {
            if r1 != r2 && region_infer_ctxt.eval_outlives((*r1).into(), (*r2).into()) {
                graph.add_edge(indices[&r1], indices[&r2], ());
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
    let regions = get_all_regions(ctxt.body(), ctxt.tcx());
    let scc_graph = compute_region_sccs(regions, ctxt.bc.region_infer_ctxt());
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
