use rustc_interface::{
    ast::Mutability,
    borrowck::consumers::{LocationTable, PoloniusOutput},
    data_structures::fx::FxHashSet,
    middle::mir::{self, BasicBlock, Local, Location},
    middle::ty::{Region, TyCtxt},
};
use serde_json::json;
use std::cmp::Ordering;

use crate::{
    borrows::domain::AbstractionInputTarget,
    coupling, rustc_interface,
    utils::{Place, PlaceRepacker},
};

use super::{
    borrows_edge::{BorrowsEdge, BorrowsEdgeKind, ToBorrowsEdge},
    borrows_state::{RegionProjectionMember, RegionProjectionMemberDirection},
    borrows_visitor::DebugCtx,
    coupling_graph_constructor::{CGNode, CouplingGraphConstructor},
    deref_expansion::DerefExpansion,
    domain::{
        AbstractionBlockEdge, AbstractionOutputTarget, AbstractionTarget, AbstractionType,
        LoopAbstraction, MaybeOldPlace, MaybeRemotePlace, Reborrow, ToJsonWithRepacker,
    },
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection::{HasRegionProjections, RegionProjection},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BorrowsGraph<'tcx>(FxHashSet<BorrowsEdge<'tcx>>);

impl<'tcx> BorrowsGraph<'tcx> {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn new() -> Self {
        Self(FxHashSet::default())
    }

    pub fn edge_count(&self) -> usize {
        self.0.len()
    }

    pub fn edges(&self) -> impl Iterator<Item = &BorrowsEdge<'tcx>> {
        self.0.iter()
    }

    pub fn abstraction_edges(&self) -> FxHashSet<Conditioned<AbstractionEdge<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowsEdgeKind::Abstraction(abstraction) => Some(Conditioned {
                    conditions: edge.conditions().clone(),
                    value: abstraction.clone(),
                }),
                _ => None,
            })
            .collect()
    }

    pub fn deref_expansions(&self) -> FxHashSet<Conditioned<DerefExpansion<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowsEdgeKind::DerefExpansion(de) => Some(Conditioned {
                    conditions: edge.conditions().clone(),
                    value: de.clone(),
                }),
                _ => None,
            })
            .collect()
    }

    pub fn reborrows(&self) -> FxHashSet<Conditioned<Reborrow<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowsEdgeKind::Reborrow(reborrow) => Some(Conditioned {
                    conditions: edge.conditions().clone(),
                    value: reborrow.clone(),
                }),
                _ => None,
            })
            .collect()
    }

    pub fn has_reborrow_at_location(&self, location: Location) -> bool {
        self.0.iter().any(|edge| match &edge.kind() {
            BorrowsEdgeKind::Reborrow(reborrow) => reborrow.reserve_location() == location,
            _ => false,
        })
    }

    pub fn reborrows_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<Conditioned<Reborrow<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowsEdgeKind::Reborrow(reborrow) => {
                    if reborrow.assigned_place == place {
                        Some(Conditioned {
                            conditions: edge.conditions().clone(),
                            value: reborrow.clone(),
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect()
    }

    pub fn is_leaf_edge(
        &self,
        edge: &BorrowsEdge<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        edge.kind()
            .blocked_by_places(repacker)
            .iter()
            .all(|p| !self.has_edge_blocking(*p))
    }

    pub fn leaf_edges(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BorrowsEdge<'tcx>> {
        let mut candidates = self.0.clone();
        candidates.retain(|edge| self.is_leaf_edge(edge, repacker));
        candidates
    }

    pub fn leaf_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.leaf_edges(repacker)
            .into_iter()
            .flat_map(|edge| edge.blocked_by_places(repacker).into_iter())
            .collect()
    }

    pub fn num_paths_between(
        &self,
        blocking: MaybeOldPlace<'tcx>,
        blocked: MaybeRemotePlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> usize {
        let mut count = 0;
        for blocked_edge in self.edges_blocked_by(blocking.into(), repacker) {
            for blocked_place in blocked_edge.blocked_places() {
                if blocked_place == blocked {
                    count += 1;
                } else {
                    if let Some(blocked_place) = blocked_place.as_local() {
                        count += self.num_paths_between(blocked_place, blocked, repacker);
                    }
                }
            }
        }
        count
    }

    pub fn assert_invariants_satisfied(&self, repacker: PlaceRepacker<'_, 'tcx>) {
        for root_edge in self.root_edges(repacker) {
            match root_edge.kind() {
                BorrowsEdgeKind::Reborrow(_reborrow) => {
                    // assert!(!reborrow.blocked_place.is_old())
                }
                BorrowsEdgeKind::DerefExpansion(_deref_expansion) => {}
                BorrowsEdgeKind::Abstraction(_abstraction_edge) => {}
                BorrowsEdgeKind::RegionProjectionMember(_region_projection_member) => {}
            }
        }

        for abstraction_edge in self.abstraction_edges().into_iter() {
            match abstraction_edge.value.abstraction_type {
                AbstractionType::FunctionCall(_function_call_abstraction) => {}
                AbstractionType::Loop(loop_abstraction) => {
                    for input in loop_abstraction.inputs() {
                        match input {
                            AbstractionTarget::Place(MaybeRemotePlace::Local(place)) => {
                                if place.is_old() {
                                    for rb in self.reborrows_blocked_by(place) {
                                        if let Some(local_place) = rb.value.blocked_place.as_local()
                                        {
                                            assert!(
                                                !local_place.is_old(),
                                                "old input of loop abstraction {:?} blocks old place {:?}",
                                                input,
                                                local_place
                                            );
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    pub fn root_edges(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BorrowsEdge<'tcx>> {
        self.0
            .iter()
            .filter(|edge| {
                edge.blocked_places().iter().all(|p| match p {
                    MaybeRemotePlace::Local(maybe_old_place) => {
                        self.is_root(*maybe_old_place, repacker)
                    }
                    MaybeRemotePlace::Remote(_local) => true,
                })
            })
            .cloned()
            .collect::<FxHashSet<_>>()
    }

    pub fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.root_edges(repacker)
            .into_iter()
            .flat_map(|edge| edge.blocked_places().into_iter())
            .collect()
    }

    pub fn has_edge_blocking(&self, place: MaybeOldPlace<'tcx>) -> bool {
        self.0
            .iter()
            .any(|edge| edge.blocked_places().contains(&(place.into())))
    }

    pub fn is_root(&self, place: MaybeOldPlace<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        !self.has_edge_blocked_by(place, repacker)
    }

    pub fn has_edge_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.0
            .iter()
            .any(|edge| edge.blocked_by_places(repacker).contains(&place))
    }

    pub fn edges_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<BorrowsEdge<'tcx>> {
        self.0
            .iter()
            .filter(|edge| edge.blocked_by_places(repacker).contains(&place))
            .cloned()
            .collect()
    }

    pub fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest,
        _debug_ctx: Option<DebugCtx>,
    ) {
        self.mut_edges(|edge| {
            edge.make_place_old(place, latest);
            true
        });
    }

    // pub fn abstract_subgraph(
    //     &mut self,
    //     block: BasicBlock,
    //     subgraph: BorrowsGraph<'tcx>,
    //     repacker: PlaceRepacker<'_, 'tcx>,
    // ) {
    //     self.assert_invariants_satisfied(repacker);
    //     for edge in subgraph.edges() {
    //         self.remove(edge, DebugCtx::Other);
    //     }
    //     let edges = subgraph
    //         .leaf_edges(repacker)
    //         .into_iter()
    //         .flat_map(|edge| {
    //             edge.blocked_by_places(repacker)
    //                 .into_iter()
    //                 .flat_map(|place| {
    //                     let blocked_roots = subgraph.roots_blocked_by(place, repacker);
    //                     blocked_roots
    //                         .into_iter()
    //                         .filter(|blocked_root| !blocked_root.is_old())
    //                         .map(|blocked_root| {
    //                             AbstractionBlockEdge::new(
    //                                 vec![AbstractionTarget::Place(blocked_root)]
    //                                     .into_iter()
    //                                     .collect(),
    //                                 vec![AbstractionTarget::Place(place)].into_iter().collect(),
    //                             )
    //                         })
    //                         .collect::<Vec<_>>()
    //                 })
    //         })
    //         .collect();
    //     let abstraction = LoopAbstraction::new(edges, block);
    //     self.insert(
    //         AbstractionEdge::new(AbstractionType::Loop(abstraction))
    //             .to_borrows_edge(PathConditions::new(block)),
    //     );
    //     self.assert_invariants_satisfied(repacker);
    // }

    pub fn roots_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.edges_blocked_by(place, repacker)
            .into_iter()
            .flat_map(|edge| {
                edge.blocked_places().into_iter().flat_map(|p| match p {
                    MaybeRemotePlace::Local(maybe_old_place) => {
                        if self.is_root(maybe_old_place, repacker) {
                            vec![p].into_iter().collect()
                        } else {
                            self.roots_blocked_by(maybe_old_place, repacker)
                        }
                    }
                    MaybeRemotePlace::Remote(_local) => vec![p].into_iter().collect(),
                })
            })
            .collect()
    }

    fn construct_coupling_graph(
        &self,
        output_facts: &PoloniusOutput,
        location_table: &LocationTable,
        repacker: PlaceRepacker<'_, 'tcx>,
        block: BasicBlock,
        leaf_nodes: FxHashSet<MaybeOldPlace<'tcx>>,
    ) -> (coupling::Graph<CGNode<'tcx>>, FxHashSet<BorrowsEdge<'tcx>>) {
        let constructor =
            CouplingGraphConstructor::new(output_facts, location_table, repacker, block);
        constructor.construct_coupling_graph(self, leaf_nodes)
    }

    fn join_loop(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        exit_block: BasicBlock,
        repacker: PlaceRepacker<'_, 'tcx>,
        output_facts: &PoloniusOutput,
        location_table: &LocationTable,
    ) -> bool {
        let self_leaf_nodes = self.leaf_nodes(repacker);
        let other_leaf_nodes = other.leaf_nodes(repacker);
        let (self_coupling_graph, self_to_remove) = self.construct_coupling_graph(
            output_facts,
            location_table,
            repacker,
            exit_block,
            self_leaf_nodes,
        );
        let (other_coupling_graph, _) = other.construct_coupling_graph(
            output_facts,
            location_table,
            repacker,
            exit_block,
            other_leaf_nodes,
        );
        // self_coupling_graph.render_with_imgcat().unwrap();
        // other_coupling_graph.render_with_imgcat().unwrap();
        let hypergraph =
            coupling::coupling_algorithm(self_coupling_graph, other_coupling_graph).unwrap();
        // eprintln!("Result: {:?}", hypergraph);
        let mut changed = false;
        for edge in self_to_remove.iter() {
            if self.remove(edge, DebugCtx::Other) {
                changed = true;
            }
        }
        for edge in hypergraph.edges() {
            let abstraction = LoopAbstraction::new(
                AbstractionBlockEdge::new(
                    edge.rhs()
                        .iter()
                        .map(|n| n.to_abstraction_input_target())
                        .collect(),
                    edge.lhs()
                        .iter()
                        .map(|n| n.to_abstraction_output_target())
                        .collect(),
                ),
                self_block,
            )
            .to_borrows_edge(PathConditions::new(self_block));
            if self.insert(abstraction) {
                changed = true;
            }
        }
        return changed;
    }

    pub fn join(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        output_facts: &PoloniusOutput,
        location_table: &LocationTable,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;

        // Optimization
        if repacker
            .body()
            .basic_blocks
            .dominators()
            .dominates(other_block, self_block)
        {
            if other != self {
                *self = other.clone();
                return true;
            } else {
                return false;
            }
        }
        let our_edges = self.0.clone();
        if repacker.is_back_edge(other_block, self_block) {
            let exit_blocks = repacker.get_loop_exit_blocks(self_block, other_block);
            if exit_blocks.len() == 1 {
                return self.join_loop(
                    other,
                    self_block,
                    exit_blocks[0],
                    repacker,
                    output_facts,
                    location_table,
                );
            }
            // TODO: Handle multiple exit blocks
        }
        for other_edge in other.0.iter() {
            match our_edges.iter().find(|e| e.kind() == other_edge.kind()) {
                Some(our_edge) => {
                    if our_edge.conditions() != other_edge.conditions() {
                        let mut new_conditions = our_edge.conditions().clone();
                        new_conditions.join(&other_edge.conditions());
                        self.0.remove(our_edge);
                        self.insert(BorrowsEdge::new(other_edge.kind().clone(), new_conditions));
                        changed = true;
                    }
                }
                None => {
                    self.insert(other_edge.clone());
                    changed = true;
                }
            }
        }
        let mut finished = false;
        while !finished {
            finished = true;
            for leaf_node in self.leaf_nodes(repacker) {
                eprintln!(
                    "{:?} <- {:?} Check {:?}",
                    self_block, other_block, leaf_node
                );
                if !other.leaf_nodes(repacker).contains(&leaf_node) {
                    for edge in self.edges_blocked_by(leaf_node.into(), repacker) {
                        eprintln!("Remove {:?}", edge);
                        finished = false;
                        self.remove(&edge, DebugCtx::Other);
                        changed = true;
                    }
                }
            }
        }
        changed
    }

    pub fn change_region_projection(
        &mut self,
        old_projection: RegionProjection<'tcx>,
        new_projection: RegionProjection<'tcx>,
    ) -> bool {
        todo!()
    }

    pub fn change_maybe_old_place(
        &mut self,
        old_place: MaybeOldPlace<'tcx>,
        new_place: MaybeOldPlace<'tcx>,
    ) -> bool {
        self.mut_maybe_old_places(|place| {
            if *place == old_place {
                *place = new_place;
                true
            } else {
                false
            }
        })
    }

    pub fn add_reborrow(
        &mut self,
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
        region: Region<'tcx>,
    ) -> bool {
        self.insert(
            Reborrow::new(
                blocked_place.into(),
                assigned_place.into(),
                mutability,
                location,
                region,
            )
            .to_borrows_edge(PathConditions::new(location.block)),
        )
    }

    pub fn insert(&mut self, edge: BorrowsEdge<'tcx>) -> bool {
        self.0.insert(edge)
    }

    pub fn edges_blocking(
        &self,
        place: MaybeRemotePlace<'tcx>,
    ) -> impl Iterator<Item = &BorrowsEdge<'tcx>> {
        self.0
            .iter()
            .filter(move |edge| edge.blocked_places().contains(&place))
    }

    pub fn remove_abstraction_at(&mut self, location: Location) {
        self.0.retain(|edge| {
            if let BorrowsEdgeKind::Abstraction(abstraction) = &edge.kind() {
                abstraction.location() != location
            } else {
                true
            }
        });
    }

    pub fn remove(&mut self, edge: &BorrowsEdge<'tcx>, debug_ctx: DebugCtx) -> bool {
        self.0.remove(edge)
    }

    pub fn move_region_projection_member_projections(
        &mut self,
        old_projection_place: MaybeOldPlace<'tcx>,
        new_projection_place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.mut_edges(|edge| {
            if let BorrowsEdgeKind::RegionProjectionMember(member) = &mut edge.kind {
                if member.projection.place == old_projection_place {
                    let idx = member.projection_index(repacker);
                    member.projection = new_projection_place.region_projection(idx, repacker);
                }
            }
            true
        });
    }

    pub fn move_reborrows(
        &mut self,
        orig_assigned_place: MaybeOldPlace<'tcx>,
        new_assigned_place: MaybeOldPlace<'tcx>,
    ) {
        self.mut_edges(|edge| {
            if let BorrowsEdgeKind::Reborrow(reborrow) = &mut edge.kind {
                if reborrow.assigned_place == orig_assigned_place {
                    reborrow.assigned_place = new_assigned_place;
                }
            }
            true
        });
    }

    pub fn contains_deref_expansion_from(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        self.0.iter().any(|edge| {
            if let BorrowsEdgeKind::DerefExpansion(de) = &edge.kind {
                de.base() == *place
            } else {
                false
            }
        })
    }

    pub fn ensure_deref_expansion_to_at_least(
        &mut self,
        place: Place<'tcx>,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        location: Location,
    ) {
        let mut in_dag = false;
        for (place, elem) in place.iter_projections() {
            let place: Place<'tcx> = place.into();
            if place.is_ref(body, tcx) {
                in_dag = true;
            }
            let expansion = match elem {
                mir::ProjectionElem::Downcast(_, _) | // For downcast we can't blindly expand since we don't know which instance, use this specific one
                mir::ProjectionElem::Deref // For Box we don't want to expand fields because it's actually an ADT w/ a ptr inside
                        => {
                            vec![place.project_deeper(&[elem], tcx).into()]
                        }
                        _ => place.expand_field(None, PlaceRepacker::new(&body, tcx)),
                    };
            if in_dag {
                let origin_place = place.into();
                if !self.contains_deref_expansion_from(&origin_place) {
                    self.insert_deref_expansion(
                        origin_place,
                        expansion,
                        location,
                        PlaceRepacker::new(&body, tcx),
                    );
                }
            }
        }
    }

    fn insert_deref_expansion(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        expansion: Vec<Place<'tcx>>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for p in expansion.iter() {
            assert!(p.projection.len() > place.place().projection.len());
        }
        let de = if place.place().is_owned(repacker.body(), repacker.tcx()) {
            DerefExpansion::OwnedExpansion { base: place }
        } else {
            DerefExpansion::borrowed(place, expansion, location, repacker)
        };
        self.insert(BorrowsEdge::new(
            BorrowsEdgeKind::DerefExpansion(de),
            PathConditions::new(location.block),
        ));
    }

    fn mut_region_projections(
        &mut self,
        mut f: impl FnMut(&mut MaybeOldPlace<'tcx>) -> bool,
    ) -> bool {
        todo!()
        // self.mut_edges(|edge| {
        //     let maybe_old_places: Vec<&mut MaybeOldPlace<'tcx>> = match edge.mut_kind() {
        //         BorrowsEdgeKind::Reborrow(reborrow) => {
        //             let mut vec = vec![&mut reborrow.assigned_place];
        //             if let ReborrowBlockedPlace::Local(p) = &mut reborrow.blocked_place {
        //                 vec.push(p);
        //             }
        //             vec
        //         }
        //         BorrowsEdgeKind::DerefExpansion(de) => vec![de.mut_base()],
        //         BorrowsEdgeKind::Abstraction(ra) => ra.maybe_old_places(),
        //         BorrowsEdgeKind::RegionProjectionMember(rpm) => rpm.maybe_old_places(),
        //     };
        //     let mut changed = false;
        //     for p in maybe_old_places {
        //         if f(p) {
        //             changed = true;
        //         }
        //     }
        //     changed
        // })
    }

    fn mut_maybe_old_places(
        &mut self,
        mut f: impl FnMut(&mut MaybeOldPlace<'tcx>) -> bool,
    ) -> bool {
        self.mut_edges(|edge| {
            let maybe_old_places: Vec<&mut MaybeOldPlace<'tcx>> = match edge.mut_kind() {
                BorrowsEdgeKind::Reborrow(reborrow) => {
                    let mut vec = vec![&mut reborrow.assigned_place];
                    if let MaybeRemotePlace::Local(p) = &mut reborrow.blocked_place {
                        vec.push(p);
                    }
                    vec
                }
                BorrowsEdgeKind::DerefExpansion(de) => vec![de.mut_base()],
                BorrowsEdgeKind::Abstraction(ra) => ra.maybe_old_places(),
                BorrowsEdgeKind::RegionProjectionMember(rpm) => rpm.maybe_old_places(),
            };
            let mut changed = false;
            for p in maybe_old_places {
                if f(p) {
                    changed = true;
                }
            }
            changed
        })
    }
    fn mut_edges(&mut self, mut f: impl FnMut(&mut BorrowsEdge<'tcx>) -> bool) -> bool {
        let mut changed = false;
        self.0 = self
            .0
            .drain()
            .map(|mut edge| {
                if f(&mut edge) {
                    changed = true;
                }
                edge
            })
            .collect();
        changed
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.0.retain(|edge| edge.conditions().valid_for_path(path));
    }

    pub fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.mut_edges(|edge| edge.insert_path_condition(pc.clone()))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Conditioned<T> {
    pub conditions: PathConditions,
    pub value: T,
}

impl<T> Conditioned<T> {
    pub fn new(value: T, conditions: PathConditions) -> Self {
        Self { conditions, value }
    }
}

impl<'tcx, T: ToJsonWithRepacker<'tcx>> ToJsonWithRepacker<'tcx> for Conditioned<T> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "conditions": self.conditions.to_json(repacker),
            "value": self.value.to_json(repacker)
        })
    }
}
