use std::collections::BTreeSet;

use smallvec::SmallVec;

use super::{
    domain::AbstractionOutputTarget,
    edge::kind::BorrowPCGEdgeKind,
    graph::{coupling_imgcat_debug, BorrowsGraph},
    has_pcs_elem::HasPcgElems,
    region_projection::PcgRegion,
};
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::{
    coupling,
    pcg::PCGNode,
    pcg_validity_assert,
    rustc_interface::data_structures::fx::FxHashSet,
    rustc_interface::middle::mir::{BasicBlock, Location},
    rustc_interface::middle::ty,
    utils::{display::DisplayWithRepacker, validity::HasValidityCheck, CompilerCtxt},
};
use crate::{utils::place::maybe_old::MaybeOldPlace, BodyAndBorrows};

/// A collection of coupled PCG nodes. They will expire at the same time, and only one
/// node in the set will be alive.
///
/// These nodes are introduced for loops: place `a` may borrow from `b` or place
/// `b` may borrow from `a` depending on the number of loop iterations. Therefore,
/// `a` and `b` are coupled and only one can be accessed.
///
/// Internally, the nodes are stored in a `Vec` to allow for mutation
#[derive(Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Coupled<T>(SmallVec<[T; 4]>);

impl<'tcx, T: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for Coupled<T> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        for t in self.0.iter() {
            t.check_validity(repacker)?;
        }
        Ok(())
    }
}

impl<'tcx, T: DisplayWithRepacker<'tcx>> DisplayWithRepacker<'tcx> for Coupled<T> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
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

// pub(crate) type AbstractionGraph<'tcx> = coupling::DisjointSetGraph<CGNode<'tcx>, FxHashSet<BorrowPCGEdge<'tcx>>>;
pub(crate) type AbstractionGraph<'tcx> =
    coupling::DisjointSetGraph<CGNode<'tcx>, BorrowPCGEdgeKind<'tcx>>;

impl<T: Clone> Coupled<T> {
    pub fn size(&self) -> usize {
        self.0.len()
    }

    pub fn singleton(item: T) -> Self {
        let mut sv = SmallVec::new();
        sv.push(item);
        Self(sv)
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
    type IntoIter = <SmallVec<[T; 4]> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
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

impl<T: Ord> From<Vec<T>> for Coupled<T> {
    fn from(vec: Vec<T>) -> Self {
        let mut bts = BTreeSet::new();
        for item in vec {
            bts.insert(item);
        }
        Self(bts.into_iter().collect())
    }
}

pub type CGNode<'tcx> = PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>;

impl<'tcx> From<AbstractionOutputTarget<'tcx>> for CGNode<'tcx> {
    fn from(target: AbstractionOutputTarget<'tcx>) -> Self {
        CGNode::RegionProjection(target.into())
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for CGNode<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            CGNode::Place(p) => p.pcg_elems(),
            CGNode::RegionProjection(rp) => rp.base.pcg_elems(),
        }
    }
}

impl<'tcx> From<CGNode<'tcx>> for PCGNode<'tcx> {
    fn from(node: CGNode<'tcx>) -> Self {
        match node {
            CGNode::Place(p) => p.into(),
            CGNode::RegionProjection(rp) => PCGNode::RegionProjection(rp.into()),
        }
    }
}
impl CGNode<'_> {
    pub(crate) fn is_old(&self) -> bool {
        match self {
            CGNode::Place(p) => p.is_old(),
            CGNode::RegionProjection(rp) => rp.base().is_old(),
        }
    }
}

pub trait BorrowCheckerInterface<'mir, 'tcx: 'mir> {
    fn new<T: BodyAndBorrows<'tcx>>(tcx: ty::TyCtxt<'tcx>, body: &'mir T) -> Self
    where
        Self: Sized;

    /// Returns true if the node is live *before* `location`.
    fn is_live(&self, node: PCGNode<'tcx>, location: Location) -> bool;
    fn is_dead(&self, node: PCGNode<'tcx>, location: Location) -> bool {
        !self.is_live(node, location)
    }
    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool;

    fn same_region(&self, reg1: PcgRegion, reg2: PcgRegion) -> bool {
        self.outlives(reg1, reg2) && self.outlives(reg2, reg1)
    }

    /// Returns the set of two-phase borrows that activate at `location`.
    /// Each borrow in the returned set is represented by the MIR location
    /// that it was created at.
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

pub(crate) struct AbstractionGraphConstructor<'mir, 'tcx> {
    repacker: CompilerCtxt<'mir, 'tcx>,
    #[allow(unused)]
    block: BasicBlock,
    graph: AbstractionGraph<'tcx>,
}

#[derive(Clone, Eq, PartialEq)]
struct AddEdgeHistory<'a, 'tcx> {
    bottom_connect: &'a Coupled<CGNode<'tcx>>,
    upper_candidate: &'a Coupled<CGNode<'tcx>>,
}

impl std::fmt::Display for AddEdgeHistory<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "bottom: {{{}}}, upper: {{{}}}",
            self.bottom_connect
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<_>>()
                .join(", "),
            self.upper_candidate
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<'mir, 'tcx> AbstractionGraphConstructor<'mir, 'tcx> {
    pub(crate) fn new(repacker: CompilerCtxt<'mir, 'tcx>, block: BasicBlock) -> Self {
        Self {
            repacker,
            block,
            graph: AbstractionGraph::new(),
        }
    }

    fn add_edges_from<'a>(
        &mut self,
        bg: &AbstractionGraph<'tcx>,
        bottom_connect: &'a Coupled<CGNode<'tcx>>,
        upper_candidate: &'a Coupled<CGNode<'tcx>>,
        mut weight: FxHashSet<BorrowPCGEdgeKind<'tcx>>,
        borrow_checker: &dyn BorrowCheckerInterface<'mir, 'tcx>,
        mut history: DebugRecursiveCallHistory<AddEdgeHistory<'a, 'tcx>>,
    ) {
        history.add(AddEdgeHistory {
            bottom_connect,
            upper_candidate,
        });
        let upper_candidate = upper_candidate.clone();
        let endpoints = bg.parents(&upper_candidate);
        for (coupled, edge_weight) in endpoints {
            weight.extend(edge_weight);
            pcg_validity_assert!(
                coupled != upper_candidate,
                "Coupling graph should be acyclic"
            );
            let is_root = bg.is_root(&coupled) && !coupled.iter().any(|n| n.is_old());
            let should_include = is_root
                || coupled.iter().any(|n| {
                    let is_live = borrow_checker.is_live(
                        (*n).into(),
                        Location {
                            block: self.block,
                            statement_index: 0,
                        },
                    );
                    is_live && !n.is_old()
                });
            if !should_include {
                self.add_edges_from(
                    bg,
                    bottom_connect,
                    &coupled,
                    weight.clone(),
                    borrow_checker,
                    history.clone(),
                );
            } else {
                self.graph.add_edge(
                    &coupled,
                    &bottom_connect.clone(),
                    weight.clone(),
                    self.repacker,
                );
                self.add_edges_from(
                    bg,
                    &coupled,
                    &coupled,
                    FxHashSet::default(),
                    borrow_checker,
                    history.clone(),
                );
            }
        }
    }

    pub(crate) fn construct_abstraction_graph(
        mut self,
        bg: &BorrowsGraph<'tcx>,
        borrow_checker: &dyn BorrowCheckerInterface<'mir, 'tcx>,
    ) -> AbstractionGraph<'tcx> {
        tracing::debug!("Construct coupling graph start");
        let full_graph = bg.base_rp_graph(self.repacker);
        if coupling_imgcat_debug() {
            full_graph.render_with_imgcat(self.repacker, "Base coupling graph");
        }
        let leaf_nodes = full_graph.leaf_nodes();
        let num_leaf_nodes = leaf_nodes.len();
        for (i, node) in leaf_nodes.into_iter().enumerate() {
            tracing::debug!("Inserting leaf node {} / {}", i, num_leaf_nodes);
            self.graph.insert_endpoint(node.clone(), self.repacker);
            self.add_edges_from(
                &full_graph,
                &node,
                &node,
                FxHashSet::default(),
                borrow_checker,
                DebugRecursiveCallHistory::new(),
            );
        }
        tracing::debug!("Construct coupling graph end");
        self.graph
    }
}
