use std::cmp::Ordering;

use crate::{
    coupling,
    rustc_interface::{
        ast::Mutability,
        borrowck::consumers::{LocationTable, PoloniusOutput},
        data_structures::fx::FxHashSet,
        middle::{
            mir::{self, BasicBlock, Local, Location},
            ty::{Region, TyCtxt},
        },
    },
    utils::{Place, PlaceRepacker},
};

use super::{
    borrows_graph::{BorrowsEdge, BorrowsEdgeKind, BorrowsGraph},
    domain::{
        AbstractionInputTarget, AbstractionOutputTarget, MaybeOldPlace, ReborrowBlockedPlace,
    },
};

#[derive(Debug, Eq, Hash, PartialEq, Copy, Clone)]
pub enum CGNode<'tcx> {
    Local(Place<'tcx>),
    Remote(Local),
}

impl<'tcx> CGNode<'tcx> {
    pub fn to_abstraction_input_target(&self) -> AbstractionInputTarget<'tcx> {
        match self {
            CGNode::Local(place) => AbstractionInputTarget::Place((*place).into()),
            CGNode::Remote(local) => {
                AbstractionInputTarget::Place(ReborrowBlockedPlace::Remote(*local))
            }
        }
    }

    pub fn to_abstraction_output_target(&self) -> AbstractionOutputTarget<'tcx> {
        match self {
            CGNode::Local(place) => AbstractionOutputTarget::Place((*place).into()),
            CGNode::Remote(_) => {
                unreachable!()
            }
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
        bg: &BorrowsGraph<'tcx>,
        path_edges: FxHashSet<BorrowsEdge<'tcx>>,
        from: Place<'tcx>,
        curr: MaybeOldPlace<'tcx>,
    ) {
        let edges = bg.edges_blocked_by(curr, self.repacker);
        for edge in edges {
            let mut new_path_edges = path_edges.clone();
            new_path_edges.insert(edge.clone());
            match edge.kind() {
                BorrowsEdgeKind::Reborrow(reborrow) => match reborrow.blocked_place {
                    ReborrowBlockedPlace::Local(MaybeOldPlace::Current { place }) => {
                        let live_origins =
                            self.output_facts
                                .origins_live_at(self.location_table.start_index(Location {
                                    block: self.block,
                                    statement_index: 0,
                                }));
                        eprintln!("reborrow region: {:?}", reborrow.region);
                        self.coupling_graph
                            .add_edge(CGNode::Local(from), CGNode::Local(place));
                        self.to_remove.extend(new_path_edges);
                        self.add_edges_from(bg, FxHashSet::default(), place.into(), place.into());
                    }
                    ReborrowBlockedPlace::Local(old_place) => {
                        self.add_edges_from(bg, new_path_edges, from, old_place)
                    }
                    ReborrowBlockedPlace::Remote(local) => {
                        self.to_remove.extend(new_path_edges);
                        self.coupling_graph
                            .add_edge(CGNode::Local(from), CGNode::Remote(local));
                    }
                },
                BorrowsEdgeKind::DerefExpansion(de) => {
                    self.add_edges_from(bg, new_path_edges, from, de.base());
                }
                BorrowsEdgeKind::Abstraction(_) => {
                    // TODO
                }
                BorrowsEdgeKind::RegionProjectionMember(_) => todo!(),
            }
        }
    }

    pub fn construct_coupling_graph(
        mut self,
        bg: &BorrowsGraph<'tcx>,
        leaf_nodes: FxHashSet<MaybeOldPlace<'tcx>>,
    ) -> (coupling::Graph<CGNode<'tcx>>, FxHashSet<BorrowsEdge<'tcx>>) {
        for node in leaf_nodes {
            match node {
                MaybeOldPlace::Current { place } => {
                    self.add_edges_from(bg, FxHashSet::default(), place, node)
                }
                MaybeOldPlace::OldPlace(_) => unreachable!(),
            }
        }
        (self.coupling_graph, self.to_remove)
    }
}
