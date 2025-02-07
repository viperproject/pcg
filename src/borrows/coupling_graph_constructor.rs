use std::{
    cmp::Ordering,
    collections::{BTreeSet, HashSet},
};

use crate::{
    combined_pcs::{PCGNode, PCGNodeLike},
    coupling,
    rustc_interface::middle::mir::{BasicBlock, Location},
    utils::{display::DisplayWithRepacker, validity::HasValidityCheck, PlaceRepacker},
    ToJsonWithRepacker,
};

use super::{
    borrow_pcg_edge::LocalNode,
    borrows_graph::{coupling_imgcat_debug, BorrowsGraph},
    domain::{MaybeOldPlace, MaybeRemotePlace, RemotePlace},
    has_pcs_elem::HasPcsElems,
    region_projection::{PCGRegion, RegionProjection},
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

impl<'tcx, T: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for Coupled<T> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        for t in self.0.iter() {
            t.check_validity(repacker)?;
        }
        Ok(())
    }
}

impl<'tcx, T: DisplayWithRepacker<'tcx>> DisplayWithRepacker<'tcx> for Coupled<T> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "{{{}}}",
            self.0
                .iter()
                .map(|t| t.to_short_string(repacker))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

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
    pub fn size(&self) -> usize {
        self.0.len()
    }

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

    pub(crate) fn merge(&mut self, other: Self) {
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

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum CGNode<'tcx> {
    RegionProjection(RegionProjection<'tcx>),
    RemotePlace(RemotePlace),
}

impl<'tcx> PCGNodeLike<'tcx> for CGNode<'tcx> {
    fn to_pcg_node(self) -> PCGNode<'tcx> {
        match self {
            CGNode::RegionProjection(rp) => rp.into(),
            CGNode::RemotePlace(rp) => rp.into(),
        }
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for CGNode<'tcx> {
    fn to_short_string(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> String {
        todo!()
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for CGNode<'tcx> {
    fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        todo!()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for CGNode<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        match self {
            CGNode::RegionProjection(rp) => rp.check_validity(repacker),
            CGNode::RemotePlace(rp) => rp.check_validity(repacker),
        }
    }
}
impl<'tcx> TryFrom<MaybeRemotePlace<'tcx>> for CGNode<'tcx> {
    type Error = ();
    fn try_from(node: MaybeRemotePlace<'tcx>) -> Result<Self, Self::Error> {
        match node {
            MaybeRemotePlace::Remote(rp) => Ok(CGNode::RemotePlace(rp)),
            MaybeRemotePlace::Local(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<PCGNode<'tcx>> for CGNode<'tcx> {
    type Error = ();
    fn try_from(node: PCGNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            PCGNode::Place(p) => Ok(p.try_into()?),
            PCGNode::RegionProjection(rp) => Ok(CGNode::RegionProjection(rp.into())),
        }
    }
}

impl<'tcx> TryFrom<LocalNode<'tcx>> for CGNode<'tcx> {
    type Error = ();
    fn try_from(node: LocalNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            LocalNode::Place(_) => Err(()),
            LocalNode::RegionProjection(rp) => Ok(CGNode::RegionProjection(rp.into())),
        }
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for CGNode<'tcx> {
    fn from(rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        CGNode::RegionProjection(rp.into())
    }
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

impl<'tcx> TryFrom<CGNode<'tcx>> for RegionProjection<'tcx> {
    type Error = ();
    fn try_from(node: CGNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            CGNode::RegionProjection(rp) => Ok(rp),
            CGNode::RemotePlace(_) => Err(()),
        }
    }
}

impl<'tcx> CGNode<'tcx> {
    pub(crate) fn is_old(&self) -> bool {
        match self {
            CGNode::RegionProjection(rp) => rp.place().is_old(),
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

pub(crate) trait BorrowCheckerInterface<'tcx> {
    fn is_live(&self, node: PCGNode<'tcx>, location: Location) -> bool;
    fn outlives(&self, sup: PCGRegion, sub: PCGRegion) -> bool;

    /// Returns the set of two-phase borrows that activate at `location`.
    /// Each borrow in the returned set is represented by the MIR location
    /// that it was created at.
    /// TODO: Actually use this
    #[allow(unused)]
    fn twophase_borrow_activations(&self, location: Location) -> BTreeSet<Location>;
}

/// Records a history of actions for debugging purpose;
/// used to detect infinite recursion
#[derive(Clone)]
struct DebugRecursiveCallHistory<T> {
    #[cfg(debug_assertions)]
    history: Vec<T>,
    #[cfg(not(debug_assertions))]
    _marker: std::marker::PhantomData<T>,
}

#[cfg(debug_assertions)]
impl<T> DebugRecursiveCallHistory<T> {
    fn new() -> Self {
        Self { history: vec![] }
    }

    fn add(&mut self, action: T)
    where
        T: std::cmp::Eq + std::fmt::Display,
    {
        if self.history.contains(&action) {
            panic!(
                "Infinite recursion adding:\n{}, to path:\n{}",
                action,
                self.history
                    .iter()
                    .map(|a| format!("{}", a))
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
        self.history.push(action);
    }
}

#[cfg(not(debug_assertions))]
impl<T> DebugRecursiveCallHistory<T> {
    fn new() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }

    fn add(&mut self, _action: T) {}
}

pub(crate) struct CouplingGraphConstructor<'regioncx, 'mir, 'tcx, T> {
    #[allow(unused)]
    liveness: &'regioncx T,
    repacker: PlaceRepacker<'mir, 'tcx>,
    #[allow(unused)]
    block: BasicBlock,
    coupling_graph: coupling::DisjointSetGraph<CGNode<'tcx>>,
}

#[derive(Clone, Eq, PartialEq)]
struct AddEdgeHistory<'a, 'tcx> {
    bottom_connect: &'a BTreeSet<CGNode<'tcx>>,
    upper_candidate: &'a BTreeSet<CGNode<'tcx>>,
}

impl<'a, 'tcx> std::fmt::Display for AddEdgeHistory<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "bottom: {}, upper: {}",
            format!(
                "{{{}}}",
                self.bottom_connect
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            format!(
                "{{{}}}",
                self.upper_candidate
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        )
    }
}

impl<'regioncx, 'mir, 'tcx, T: BorrowCheckerInterface<'tcx>>
    CouplingGraphConstructor<'regioncx, 'mir, 'tcx, T>
{
    pub(crate) fn new(
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

    fn add_edges_from<'a>(
        &mut self,
        bg: &coupling::DisjointSetGraph<CGNode<'tcx>>,
        bottom_connect: &'a BTreeSet<CGNode<'tcx>>,
        upper_candidate: &'a BTreeSet<CGNode<'tcx>>,
        mut history: DebugRecursiveCallHistory<AddEdgeHistory<'a, 'tcx>>,
    ) {
        history.add(AddEdgeHistory {
            bottom_connect,
            upper_candidate,
        });
        let upper_candidate = upper_candidate.clone().into();
        let endpoints = bg.endpoints_pointing_to(&upper_candidate);
        for coupled in endpoints {
            debug_assert!(
                coupled != upper_candidate,
                "Coupling graph should be acyclic"
            );
            let should_include = coupled
                .iter()
                .any(|n| /* self.liveness.is_live(*n, self.block) && */ !n.is_old());
            let coupled_set: BTreeSet<_> = coupled.clone().into_iter().collect();
            if !should_include {
                self.add_edges_from(bg, &bottom_connect, &coupled_set, history.clone());
            } else {
                self.coupling_graph
                    .add_edge(&coupled, &bottom_connect.clone().into());
                self.add_edges_from(bg, &coupled_set, &coupled_set, history.clone());
            }
        }
    }

    pub(crate) fn construct_coupling_graph(
        mut self,
        bg: &BorrowsGraph<'tcx>,
    ) -> coupling::DisjointSetGraph<CGNode<'tcx>> {
        let full_graph = bg.base_coupling_graph(self.repacker);
        if coupling_imgcat_debug() {
            full_graph.render_with_imgcat("Base coupling graph");
        }
        let leaf_nodes = full_graph.leaf_nodes();
        for node in leaf_nodes {
            self.coupling_graph.insert_endpoint(node.clone());
            let node_set: BTreeSet<_> = node.into_iter().collect();
            self.add_edges_from(
                &full_graph,
                &node_set,
                &node_set,
                DebugRecursiveCallHistory::new(),
            );
        }
        self.coupling_graph
    }
}
