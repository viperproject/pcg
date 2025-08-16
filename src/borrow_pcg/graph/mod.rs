//! Defines the Borrow PCG Graph
pub(crate) mod aliases;
pub(crate) mod frozen;
pub(crate) mod join;
pub(crate) mod loop_abstraction;
pub(crate) mod materialize;
mod mutate;

use crate::{
    borrow_pcg::{
        has_pcs_elem::{LabelLifetimeProjection, LabelLifetimeProjectionPredicate},
        region_projection::LifetimeProjectionLabel,
    },
    error::PcgUnsupportedError,
    owned_pcg::ExpandedPlace,
    pcg::{PCGNodeLike, PcgNode},
    rustc_interface::{
        data_structures::fx::{FxHashMap, FxHashSet},
        middle::mir::{self},
    },
    utils::{
        DEBUG_BLOCK, DEBUG_IMGCAT, DebugImgcat, HasBorrowCheckerCtxt, HasCompilerCtxt, Place,
        data_structures::HashSet,
        display::{DebugLines, DisplayWithCompilerCtxt},
        maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
};
use frozen::{CachedLeafEdges, FrozenGraphRef};
use itertools::Itertools;
use serde_json::json;

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, BorrowPcgEdgeLike, BorrowPcgEdgeRef, LocalNode},
    edge::borrow::LocalBorrow,
    edge_data::EdgeData,
    path_condition::ValidityConditions,
};
use crate::borrow_pcg::edge::abstraction::AbstractionType;
use crate::borrow_pcg::edge::borrow::BorrowEdge;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::utils::CompilerCtxt;
use crate::utils::json::ToJsonWithCompilerCtxt;

/// The Borrow PCG Graph.
#[derive(Clone, Debug, Default)]
pub struct BorrowsGraph<'tcx> {
    edges: FxHashMap<BorrowPcgEdgeKind<'tcx>, ValidityConditions>,
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for BorrowsGraph<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        self.edges()
            .map(|edge| edge.to_short_string(repacker).to_string())
            .sorted()
            .collect()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowsGraph<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        let nodes = self.nodes(ctxt);
        // TODO
        for node in nodes.iter() {
            if let Some(PcgNode::LifetimeProjection(rp)) = node.try_to_local_node(ctxt)
                && rp.is_future()
                && rp.base.as_current_place().is_some()
            {
                let current_rp = rp.with_label(None, ctxt);
                let conflicting_edges = self
                    .edges_blocking(current_rp.into(), ctxt)
                    .chain(self.edges_blocked_by(current_rp.into(), ctxt))
                    .collect::<HashSet<_>>();
                if !conflicting_edges.is_empty() {
                    return Err(format!(
                        "Placeholder region projection {} has edges blocking or blocked by its current version {}:\n\t{}",
                        rp.to_short_string(ctxt),
                        current_rp.to_short_string(ctxt),
                        conflicting_edges
                            .iter()
                            .map(|e| e.to_short_string(ctxt))
                            .join("\n\t")
                    ));
                }
            }
        }
        for edge in self.edges() {
            if let BorrowPcgEdgeKind::BorrowPcgExpansion(e) = edge.kind()
                && let Some(place) = e.base.as_current_place()
                && place.projects_shared_ref(ctxt)
            {
                edge.check_validity(ctxt)?;
            }
        }
        Ok(())
    }
}

impl Eq for BorrowsGraph<'_> {}

impl PartialEq for BorrowsGraph<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.edges == other.edges
    }
}

pub(crate) fn borrows_imgcat_debug(
    block: mir::BasicBlock,
    debug_imgcat: Option<DebugImgcat>,
) -> bool {
    if let Some(debug_block) = *DEBUG_BLOCK
        && debug_block != block
    {
        return false;
    }
    if let Some(debug_imgcat) = debug_imgcat {
        DEBUG_IMGCAT.contains(&debug_imgcat)
    } else {
        !DEBUG_IMGCAT.is_empty()
    }
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn places<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.nodes(ctxt)
            .into_iter()
            .filter_map(|node| match node {
                PcgNode::Place(place) => place.as_current_place(),
                _ => None,
            })
            .collect()
    }

    pub(crate) fn label_region_projection<'a>(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.filter_mut_edges(|edge| {
            edge.label_lifetime_projection(predicate, label, ctxt.bc_ctxt())
                .to_filter_mut_result()
        })
    }

    pub(crate) fn leaf_places<'a>(
        &self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.frozen_graph()
            .leaf_nodes(ctxt)
            .into_iter()
            .filter_map(|node| match node {
                PcgNode::Place(place) => place.as_current_place(),
                _ => None,
            })
            .collect()
    }

    pub(crate) fn contains_deref_edge_to(&self, place: Place<'tcx>) -> bool {
        self.edges().any(|edge| {
            if let BorrowPcgEdgeKind::Deref(e) = edge.kind {
                e.deref_place == place.into()
            } else {
                false
            }
        })
    }

    pub(crate) fn contains_borrow_pcg_expansion<'a>(
        &self,
        expanded_place: &ExpandedPlace<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<bool, PcgUnsupportedError>
    where
        'tcx: 'a,
    {
        let expanded_places = expanded_place.expansion_places(ctxt)?;
        let nodes = self.nodes(ctxt);
        Ok(expanded_places
            .into_iter()
            .all(|place| nodes.contains(&place.into())))
    }

    pub(crate) fn owned_places(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> HashSet<Place<'tcx>> {
        let mut result = HashSet::default();
        for edge in self.edges() {
            match edge.kind {
                BorrowPcgEdgeKind::Deref(e) => {
                    if let Some(base) = e.blocked_place.as_current_place()
                        && base.is_owned(ctxt)
                    {
                        result.insert(base);
                    }
                }
                BorrowPcgEdgeKind::Borrow(BorrowEdge::Local(borrow)) => {
                    if let MaybeLabelledPlace::Current(place) = borrow.blocked_place
                        && place.is_owned(ctxt)
                    {
                        result.insert(place);
                    }
                }
                _ => {}
            }
        }
        result
    }

    pub(crate) fn borrow_created_at(&self, location: mir::Location) -> Option<&LocalBorrow<'tcx>> {
        for edge in self.edges() {
            if let BorrowPcgEdgeKind::Borrow(BorrowEdge::Local(borrow)) = edge.kind
                && borrow.reserve_location() == location
            {
                return Some(borrow);
            }
        }
        None
    }

    pub(crate) fn contains<'a, T: Into<PcgNode<'tcx>>>(
        &self,
        node: T,
        repacker: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        let node = node.into();
        self.edges().any(|edge| {
            edge.blocks_node(node, repacker.bc_ctxt())
                || node
                    .as_blocking_node(repacker)
                    .map(|blocking| {
                        edge.blocked_by_nodes(repacker.bc_ctxt())
                            .contains(&blocking)
                    })
                    .unwrap_or(false)
        })
    }

    #[allow(unused)]
    pub(crate) fn into_edges(self) -> impl Iterator<Item = BorrowPcgEdge<'tcx>> {
        self.edges
            .into_iter()
            .map(|(kind, conditions)| BorrowPcgEdge { kind, conditions })
    }

    pub fn edges<'slf>(&'slf self) -> impl Iterator<Item = BorrowPcgEdgeRef<'tcx, 'slf>> + 'slf {
        self.edges
            .iter()
            .map(|(kind, conditions)| BorrowPcgEdgeRef { kind, conditions })
    }

    pub fn frozen_graph(&self) -> FrozenGraphRef<'_, 'tcx> {
        FrozenGraphRef::new(self)
    }

    pub(crate) fn abstraction_edge_kinds<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = &'slf AbstractionType<'tcx>> + 'slf {
        self.edges().filter_map(|edge| match edge.kind {
            BorrowPcgEdgeKind::Abstraction(abstraction) => Some(abstraction),
            _ => None,
        })
    }

    pub(crate) fn abstraction_edges<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = Conditioned<&'slf AbstractionType<'tcx>>> + 'slf {
        self.edges().filter_map(|edge| match edge.kind {
            BorrowPcgEdgeKind::Abstraction(abstraction) => Some(Conditioned {
                conditions: edge.conditions().clone(),
                value: abstraction,
            }),
            _ => None,
        })
    }

    /// All edges that are not blocked by any other edge. The argument
    /// `blocking_map` can be provided to use a shared cache for computation
    /// of blocking calculations. The argument should be used if this function
    /// is to be called multiple times on the same graph.
    pub(crate) fn is_leaf_edge<'graph, 'a: 'graph, 'bc: 'graph>(
        &'graph self,
        edge: &impl BorrowPcgEdgeLike<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
        blocking_map: &FrozenGraphRef<'graph, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        for n in edge.blocked_by_nodes(ctxt.bc_ctxt()) {
            if blocking_map.has_edge_blocking(n.into(), ctxt.bc_ctxt()) {
                return false;
            }
        }
        true
    }

    pub(crate) fn leaf_edges_set<'slf, 'a: 'slf, 'bc: 'slf>(
        &'slf self,
        repacker: impl HasBorrowCheckerCtxt<'a, 'tcx>,
        frozen_graph: &FrozenGraphRef<'slf, 'tcx>,
    ) -> CachedLeafEdges<'slf, 'tcx>
    where
        'tcx: 'a,
    {
        self.edges()
            .filter(move |edge| self.is_leaf_edge(edge, repacker, frozen_graph))
            .collect()
    }

    pub(crate) fn nodes<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> FxHashSet<PcgNode<'tcx>>
    where
        'tcx: 'a,
    {
        self.edges()
            .flat_map(|edge| {
                edge.blocked_nodes(ctxt.ctxt())
                    .chain(edge.blocked_by_nodes(ctxt.ctxt()).map(|node| node.into()))
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    pub(crate) fn roots(&self, repacker: CompilerCtxt<'_, 'tcx>) -> FxHashSet<PcgNode<'tcx>> {
        let roots: FxHashSet<PcgNode<'tcx>> = self
            .nodes(repacker)
            .into_iter()
            .filter(|node| self.is_root(*node, repacker))
            .collect();
        roots
    }

    pub(crate) fn is_root<T: Copy + Into<PcgNode<'tcx>>>(
        &self,
        node: T,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.contains(node.into(), ctxt)
            && match node.into().as_local_node(ctxt) {
                Some(node) => match node {
                    PcgNode::Place(place) if place.is_owned(ctxt) => true,
                    _ => !self.has_edge_blocked_by(node, ctxt),
                },
                None => true,
            }
    }

    pub(crate) fn has_edge_blocked_by(
        &self,
        node: LocalNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edges().any(|edge| edge.is_blocked_by(node, repacker))
    }

    pub fn edges_blocked_by<'graph, 'a: 'graph>(
        &'graph self,
        node: LocalNode<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> impl Iterator<Item = BorrowPcgEdgeRef<'tcx, 'graph>>
    where
        'tcx: 'a,
    {
        self.edges()
            .filter(move |edge| edge.blocked_by_nodes(ctxt.ctxt()).contains(&node))
    }

    pub(crate) fn nodes_blocked_by<'graph, 'mir: 'graph, 'bc: 'graph>(
        &'graph self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Vec<PcgNode<'tcx>> {
        self.edges_blocked_by(node, ctxt)
            .flat_map(|edge| edge.blocked_nodes(ctxt).collect::<Vec<_>>())
            .collect()
    }

    /// Returns true iff `edge` connects two nodes within an abstraction edge
    fn is_encapsulated_by_abstraction<'a>(
        &self,
        edge: &impl BorrowPcgEdgeLike<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        let ctxt = ctxt.bc_ctxt();
        'outer: for abstraction in self.abstraction_edge_kinds() {
            for blocked in edge.blocked_nodes(ctxt) {
                if !abstraction.blocks_node(blocked, ctxt) {
                    continue 'outer;
                }
            }
            for blocked_by in edge.blocked_by_nodes(ctxt) {
                if !abstraction.is_blocked_by(blocked_by, ctxt) {
                    continue 'outer;
                }
            }
            return true;
        }
        false
    }

    pub(crate) fn insert<'a>(
        &mut self,
        edge: BorrowPcgEdge<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        if let Some(conditions) = self.edges.get_mut(edge.kind()) {
            conditions.join(&edge.conditions, ctxt.body())
        } else {
            self.edges.insert(edge.kind, edge.conditions);
            true
        }
    }

    pub(crate) fn edges_blocking<'slf, 'a: 'slf, 'bc: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> impl Iterator<Item = BorrowPcgEdgeRef<'tcx, 'slf>>
    where
        'tcx: 'a,
    {
        self.edges()
            .filter(move |edge| edge.blocks_node(node, ctxt.bc_ctxt()))
    }

    pub(crate) fn edges_blocking_set<'slf, 'a: 'slf, 'bc: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Vec<BorrowPcgEdgeRef<'tcx, 'slf>>
    where
        'tcx: 'a,
    {
        self.edges_blocking(node, ctxt).collect()
    }

    pub(crate) fn remove(&mut self, edge: &BorrowPcgEdgeKind<'tcx>) -> Option<ValidityConditions> {
        self.edges.remove(edge)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct Conditioned<T> {
    pub(crate) conditions: ValidityConditions,
    pub(crate) value: T,
}

impl<T> Conditioned<T> {
    pub(crate) fn new(value: T, conditions: ValidityConditions) -> Self {
        Self { conditions, value }
    }
}

impl<'tcx, T: ToJsonWithCompilerCtxt<'tcx, BC>, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC>
    for Conditioned<T>
{
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        json!({
            "conditions": self.conditions.to_json(repacker),
            "value": self.value.to_json(repacker)
        })
    }
}
