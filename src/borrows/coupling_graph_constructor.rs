use std::cmp::Ordering;

use crate::{
    coupling,
    rustc_interface::{
        borrowck::consumers::{LocationTable, PoloniusOutput},
        middle::mir::{BasicBlock, Local, Location},
        middle::ty::RegionVid,
    },
    utils::PlaceRepacker,
};

use super::{
    borrows_graph::BorrowsGraph,
    domain::{AbstractionInputTarget, AbstractionOutputTarget},
    region_projection::RegionProjection,
};

pub type CGNode<'tcx> = RegionProjection<'tcx>;

impl<'tcx> CGNode<'tcx> {
    pub fn to_abstraction_input_target(&self) -> AbstractionInputTarget<'tcx> {
        *self
    }

    pub fn to_abstraction_output_target(&self) -> AbstractionOutputTarget<'tcx> {
        *self
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

pub trait LivenessChecker<'tcx> {
    fn is_live(&self, region_projection: RegionProjection<'tcx>, block: BasicBlock) -> bool;
}

pub struct CouplingGraphConstructor<'regioncx, 'mir, 'tcx, T> {
    liveness: &'regioncx T,
    repacker: PlaceRepacker<'mir, 'tcx>,
    block: BasicBlock,
    coupling_graph: coupling::Graph<CGNode<'tcx>>,
}

impl<'regioncx, 'mir, 'tcx, T: LivenessChecker<'tcx>>
    CouplingGraphConstructor<'regioncx, 'mir, 'tcx, T>
{
    pub fn new(
        region_liveness: &'regioncx T,
        repacker: PlaceRepacker<'mir, 'tcx>,
        block: BasicBlock,
    ) -> Self {
        Self {
            liveness: region_liveness,
            repacker,
            block,
            coupling_graph: coupling::Graph::new(),
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
            self.coupling_graph
                .add_edge(upper_candidate, bottom_connect);
        }
        for node in nodes {
            let is_dead = !self.liveness.is_live(node, self.block);
            if node.place.is_old() || is_dead {
                self.add_edges_from(bg, bottom_connect, node);
            } else {
                self.coupling_graph.add_edge(node, bottom_connect);
                self.add_edges_from(bg, node, node);
            }
        }
    }

    pub fn construct_coupling_graph(
        mut self,
        bg: &BorrowsGraph<'tcx>,
    ) -> coupling::Graph<CGNode<'tcx>> {
        let full_graph = bg.region_projection_graph(self.repacker);
        for node in full_graph.leaf_nodes() {
            self.add_edges_from(&full_graph, node, node)
        }
        self.coupling_graph
    }
}
