use std::{cmp::Ordering, collections::BTreeSet};

use crate::{
    coupling,
    rustc_interface::{ast::Mutability, middle::mir::BasicBlock},
    utils::PlaceRepacker,
};

use super::{
    borrows_graph::BorrowsGraph,
    domain::{MaybeOldPlace, RemotePlace},
    has_pcs_elem::HasPcsElems,
    region_projection::RegionProjection,
};

/// A collection of coupled PCG nodes. They will expire at the same time, and only one
/// node in the set will be alive.
///
/// These nodes are introduced for loops: place `a` may borrow from `b` or place
/// `b` may borrow from `a` depending on the number of loop iterations. Therefore,
/// `a` and `b` are coupled and only one can be accessed.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Coupled<T>(pub Vec<T>);

impl<T> Coupled<T> {
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut()
    }
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }
}

impl<'tcx> Coupled<RegionProjection<'tcx>> {
    pub fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        let mut iter = self.iter();
        let first = iter.next().unwrap().mutability(repacker);
        assert!(iter.all(|rp| rp.mutability(repacker) == first));
        first
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum CGNode<'tcx> {
    RegionProjection(RegionProjection<'tcx>),
    RemotePlace(RemotePlace),
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for CGNode<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            CGNode::RegionProjection(rp) => rp.pcs_elems(),
            CGNode::RemotePlace(_) => vec![],
        }
    }
}

impl<'tcx> From<RegionProjection<'tcx>> for CGNode<'tcx> {
    fn from(rp: RegionProjection<'tcx>) -> Self {
        CGNode::RegionProjection(rp)
    }
}

impl<'tcx> From<RemotePlace> for CGNode<'tcx> {
    fn from(rp: RemotePlace) -> Self {
        CGNode::RemotePlace(rp)
    }
}

impl<'tcx> CGNode<'tcx> {
    pub fn as_region_projection(self) -> Option<RegionProjection<'tcx>> {
        match self {
            CGNode::RegionProjection(rp) => Some(rp),
            CGNode::RemotePlace(_) => None,
        }
    }
    pub fn is_old(&self) -> bool {
        match self {
            CGNode::RegionProjection(rp) => rp.place.is_old(),
            CGNode::RemotePlace(_) => false,
        }
    }
}

impl std::fmt::Display for CGNode<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CGNode::RegionProjection(rp) => write!(f, "{}", rp),
            CGNode::RemotePlace(rp) => write!(f, "{}", rp),
        }
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

pub trait BorrowCheckerInterface<'tcx> {
    fn is_live(&self, node: CGNode<'tcx>, block: BasicBlock) -> bool;
}

pub struct CouplingGraphConstructor<'regioncx, 'mir, 'tcx, T> {
    liveness: &'regioncx T,
    repacker: PlaceRepacker<'mir, 'tcx>,
    block: BasicBlock,
    coupling_graph: coupling::DisjointSetGraph<CGNode<'tcx>>,
}

impl<'regioncx, 'mir, 'tcx, T: BorrowCheckerInterface<'tcx>>
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
            coupling_graph: coupling::DisjointSetGraph::new(),
        }
    }

    fn add_edges_from(
        &mut self,
        bg: &coupling::DisjointSetGraph<CGNode<'tcx>>,
        bottom_connect: &BTreeSet<CGNode<'tcx>>,
        upper_candidate: &BTreeSet<CGNode<'tcx>>,
    ) {
        let nodes = bg.nodes_pointing_to(&upper_candidate);
        for node in nodes {
            let should_include = node
                .iter()
                .any(|n| /* self.liveness.is_live(*n, self.block) && */ !n.is_old());
            if !should_include {
                self.add_edges_from(bg, &bottom_connect, &node);
            } else {
                self.coupling_graph.add_edge(&node, &bottom_connect);
                self.add_edges_from(bg, &node, &node);
            }
        }
    }

    pub fn construct_coupling_graph(
        mut self,
        bg: &BorrowsGraph<'tcx>,
    ) -> coupling::DisjointSetGraph<CGNode<'tcx>> {
        let full_graph = bg.base_coupling_graph(self.repacker);
        let leaf_nodes = full_graph.leaf_nodes();
        for node in leaf_nodes {
            self.coupling_graph.insert_endpoint(node.clone());
            self.add_edges_from(&full_graph, &node, &node)
        }
        self.coupling_graph
    }
}
