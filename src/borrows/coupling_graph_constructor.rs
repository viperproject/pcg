use std::cmp::Ordering;

use crate::{
    coupling,
    rustc_interface::{
        borrowck::consumers::{LocationTable, PoloniusOutput},
        data_structures::fx::FxHashSet,
        middle::{
            mir::{BasicBlock, Local, Location, PlaceElem},
            ty::{self},
        },
    },
    utils::{Place, PlaceRepacker},
};

use super::{
    borrows_edge::{BorrowsEdge, BorrowsEdgeKind},
    borrows_graph::BorrowsGraph,
    domain::{AbstractionInputTarget, AbstractionOutputTarget, MaybeOldPlace, MaybeRemotePlace},
    region_projection::RegionProjection,
};

pub type CGNode<'tcx> = RegionProjection<'tcx>;

impl<'tcx> CGNode<'tcx> {
    pub fn to_abstraction_input_target(&self) -> AbstractionInputTarget<'tcx> {
        AbstractionInputTarget::RegionProjection(*self)
    }

    pub fn to_abstraction_output_target(&self) -> AbstractionOutputTarget<'tcx> {
        AbstractionOutputTarget::RegionProjection(*self)
    }
}

impl Ord for CGNode<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd for CGNode<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(format!("{:?}", self).cmp(&format!("{:?}", other)))
    }
}

pub struct CouplingGraphConstructor<'polonius, 'mir, 'tcx> {
    output_facts: &'polonius PoloniusOutput,
    repacker: PlaceRepacker<'mir, 'tcx>,
    block: BasicBlock,
    coupling_graph: coupling::Graph<CGNode<'tcx>>,
    to_remove: FxHashSet<BorrowsEdge<'tcx>>,
    location_table: &'mir LocationTable,
}

impl<'polonius, 'mir, 'tcx> CouplingGraphConstructor<'polonius, 'mir, 'tcx> {
    pub fn new(
        polonius_output: &'polonius PoloniusOutput,
        location_table: &'mir LocationTable,
        repacker: PlaceRepacker<'mir, 'tcx>,
        block: BasicBlock,
    ) -> Self {
        Self {
            output_facts: polonius_output,
            repacker,
            block,
            coupling_graph: coupling::Graph::new(),
            to_remove: FxHashSet::default(),
            location_table,
        }
    }

    fn add_edges_from(
        &mut self,
        bg: &coupling::Graph<CGNode<'tcx>>,
        bottom_connect: RegionProjection<'tcx>,
        upper_candidate: RegionProjection<'tcx>,
    ) {
        let nodes = bg.nodes_pointing_to(upper_candidate);
        if nodes.is_empty() {
            self.coupling_graph.add_edge(upper_candidate, bottom_connect);
        }
        for node in nodes {
            let live_origins = self
                .output_facts
                .origins_live_at(self.location_table.start_index(Location {
                    block: self.block,
                    statement_index: 0,
                }));
            if node.place.is_old() || !live_origins.contains(&node.region().into()) {
                self.add_edges_from(bg, bottom_connect, node);
            } else {
                self.coupling_graph.add_edge(upper_candidate, bottom_connect);
                self.add_edges_from(bg, bottom_connect, node);
            }
        }
    }

    pub fn construct_coupling_graph(
        mut self,
        bg: &BorrowsGraph<'tcx>,
    ) -> (coupling::Graph<CGNode<'tcx>>, FxHashSet<BorrowsEdge<'tcx>>) {
        let full_graph = bg.region_projection_graph(self.repacker);
        full_graph.render_with_imgcat().unwrap();
        for node in full_graph.leaf_nodes() {
            eprintln!("leaf: {:?}", node);
            self.add_edges_from(&full_graph, node, node)
        }
        (self.coupling_graph, self.to_remove)
    }
}
