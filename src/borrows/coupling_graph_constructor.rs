use std::{
    cmp::Ordering,
    collections::{BTreeSet, HashSet},
};

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
///
/// Internally, the nodes are stored in a `Vec` to allow for mutation
#[derive(Clone, Debug, Hash)]
pub struct Coupled<T>(Vec<T>);

impl<T: std::hash::Hash + Eq> PartialEq for Coupled<T> {
    fn eq(&self, other: &Self) -> bool {
        self.elems_hash_set() == other.elems_hash_set()
    }
}

impl<T: std::hash::Hash + std::cmp::Eq> Eq for Coupled<T> {}

impl<T: Ord + std::hash::Hash + std::cmp::Eq> PartialOrd for Coupled<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.elems_btree_set().cmp(&other.elems_btree_set()))
    }
}

impl<T: Ord + std::hash::Hash + std::cmp::Eq> Ord for Coupled<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.elems_btree_set().cmp(&other.elems_btree_set())
    }
}

impl<T> Coupled<T> {
    pub fn singleton(item: T) -> Self {
        Self(vec![item])
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut()
    }
}

impl<T> IntoIterator for Coupled<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T: std::hash::Hash + std::cmp::Eq> Coupled<T> {
    pub fn elems_hash_set(&self) -> HashSet<&T> {
        self.0.iter().collect()
    }
}

impl<T: Ord> Coupled<T> {
    pub fn elems_btree_set(&self) -> BTreeSet<&T> {
        self.0.iter().collect()
    }

    pub fn contains(&self, item: &T) -> bool {
        self.0.contains(item)
    }

    pub fn merge(&mut self, other: Self) {
        for item in other.0 {
            if !self.0.contains(&item) {
                self.0.push(item);
            }
        }
    }
}

impl<T> From<BTreeSet<T>> for Coupled<T> {
    fn from(set: BTreeSet<T>) -> Self {
        Self(set.into_iter().collect())
    }
}

impl<T: Eq> From<Vec<T>> for Coupled<T> {
    fn from(vec: Vec<T>) -> Self {
        let mut deduped = Vec::new();
        for item in vec {
            if !deduped.contains(&item) {
                deduped.push(item);
            }
        }
        Self(deduped)
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
        let upper_candidate = upper_candidate.clone().into();
        let endpoints = bg.endpoints_pointing_to(&upper_candidate);
        for coupled in endpoints {
            let should_include = coupled
                .iter()
                .any(|n| /* self.liveness.is_live(*n, self.block) && */ !n.is_old());
            let coupled_set: BTreeSet<_> = coupled.clone().into_iter().collect();
            if !should_include {
                self.add_edges_from(bg, &bottom_connect, &coupled_set);
            } else {
                self.coupling_graph
                    .add_edge(&coupled, &bottom_connect.clone().into());
                self.add_edges_from(bg, &coupled_set, &coupled_set);
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
            let node_set: BTreeSet<_> = node.into_iter().collect();
            self.add_edges_from(&full_graph, &node_set, &node_set);
        }
        self.coupling_graph
    }
}
