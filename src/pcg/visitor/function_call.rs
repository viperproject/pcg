use super::PcgVisitor;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, LocalNode};
use crate::borrow_pcg::domain::FunctionCallAbstractionInput;
use crate::borrow_pcg::edge::abstraction::{
    AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction, FunctionData,
};
use crate::borrow_pcg::edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind};
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::graph::frozen::FrozenGraphRef;
use crate::borrow_pcg::graph::BorrowsGraph;
use crate::borrow_pcg::region_projection::{
    LocalRegionProjection, PcgRegion, RegionProjection, RegionProjectionBaseLike,
    RegionProjectionLabel,
};
use crate::borrow_pcg::util::ExploreFrom;
use crate::pcg::{LocalNodeLike, PCGNode, PCGNodeLike};
use crate::rustc_interface::middle::mir::{Location, Operand};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::{pcg_validity_assert, validity_assert_acyclic};

use super::PcgError;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::rustc_interface::middle::ty::{self};
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{self, CompilerCtxt, PlaceSnapshot, SnapshotLocation};

fn get_function_data<'tcx>(
    func: &Operand<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> Option<FunctionData<'tcx>> {
    match func.ty(ctxt.body(), ctxt.tcx()).kind() {
        ty::TyKind::FnDef(def_id, substs) => Some(FunctionData::new(*def_id, substs)),
        ty::TyKind::FnPtr(..) => None,
        _ => None,
    }
}

impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    #[tracing::instrument(skip(self, func, args, destination))]
    pub(super) fn make_function_call_abstraction(
        &mut self,
        func: &Operand<'tcx>,
        args: &[&Operand<'tcx>],
        destination: utils::Place<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        validity_assert_acyclic(self.pcg, location, self.ctxt);
        // This is just a performance optimization
        if self
            .pcg
            .borrow
            .graph()
            .has_function_call_abstraction_at(location)
        {
            return Ok(());
        }
        let function_data = get_function_data(func, self.ctxt);

        let path_conditions = self.pcg.borrow.path_conditions.clone();

        let mk_create_edge_action = |input: Vec<FunctionCallAbstractionInput<'tcx>>, output| {
            let edge = BorrowPcgEdge::new(
                AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                    location,
                    function_data,
                    AbstractionBlockEdge::new(input, output),
                ))
                .into(),
                path_conditions.clone(),
            );
            BorrowPCGAction::add_edge(edge, true)
        };

        // The versions of the region projections for the function inputs just
        // before they were moved out, labelled with their last modification
        // time
        let arg_region_projections = args
            .iter()
            .filter_map(|arg| arg.place())
            .flat_map(|mir_place| {
                let input_place: utils::Place<'tcx> = mir_place.into();
                let input_place = MaybeOldPlace::OldPlace(PlaceSnapshot::new(
                    input_place,
                    self.pcg.borrow.get_latest(input_place),
                ));
                input_place.region_projections(self.ctxt)
            })
            .collect::<Vec<_>>();

        // The subset of the argument region projections that are nested
        // (and labelled, since the set of borrows inside may be modified)
        let mut labelled_rps = FxHashSet::default();
        for arg in arg_region_projections.iter() {
            if arg.is_nested_under_mut_ref(self.ctxt) {
                self.pcg.borrow.label_region_projection(
                    arg,
                    Some(SnapshotLocation::before(location).into()),
                    self.ctxt,
                );
                labelled_rps
                    .insert(arg.label_projection(SnapshotLocation::before(location).into()));
            }
        }

        // let placeholder_targets = labelled_rps
        //     .iter()
        //     .flat_map(|rp| {
        //         self.pcg
        //             .borrow
        //             .graph()
        //             .identify_placeholder_target(*rp, self.ctxt)
        //     })
        //     .collect::<FxHashSet<_>>();

        validity_assert_acyclic(self.pcg, location, self.ctxt);

        let future_subgraph = get_future_subgraph(
            &labelled_rps,
            self.pcg.borrow.graph().frozen_graph(),
            self.ctxt,
        );

        self.pcg
            .borrow
            .graph
            .render_debug_graph(self.ctxt, location, "future constructed from");

        future_subgraph.render_debug_graph(self.ctxt, location, "future_subgraph");

        pcg_validity_assert!(
            future_subgraph.frozen_graph().is_acyclic(self.ctxt),
            "{:?}: Future subgraph is not acyclic",
            self.ctxt.body().span
        );

        let placeholder_targets = future_subgraph
            .roots(self.ctxt)
            .into_iter()
            .map(|root| {
                root.try_to_local_node(self.ctxt)
                    .unwrap_or_else(|| {
                        panic!(
                            "Root {:?} of future subgraph is not a local node",
                            root.to_short_string(self.ctxt)
                        )
                    })
                    .try_into_region_projection()
                    .unwrap()
            })
            .collect::<Vec<_>>();

        for edge in future_subgraph.into_edges() {
            if edge.blocked_by_nodes(self.ctxt).any(|p| match p {
                PCGNode::RegionProjection(rp) => labelled_rps.contains(&rp),
                _ => false,
            }) {
                continue;
            }
            self.pcg.borrow.graph.insert(edge, self.ctxt);
        }

        // The set of region projections that contain borrows that could be
        // moved into the labelled rps (as they are seen after the function call)
        let source_arg_projections = arg_region_projections
            .iter()
            .map(|rp| {
                if rp.is_nested_under_mut_ref(self.ctxt) {
                    (*rp).label_projection(SnapshotLocation::before(location).into())
                } else {
                    *rp
                }
            })
            .collect::<Vec<_>>();

        let disjoint_lifetime_sets = get_disjoint_lifetime_sets(&arg_region_projections, self.ctxt);
        for ls in disjoint_lifetime_sets.iter() {
            let this_region = ls.iter().next().unwrap();
            let inputs: Vec<FunctionCallAbstractionInput<'tcx>> = source_arg_projections
                .iter()
                .filter(|rp| self.ctxt.bc.outlives(rp.region(self.ctxt), *this_region))
                .copied()
                .collect::<Vec<_>>();
            let mut outputs = placeholder_targets
                .iter()
                .copied()
                .filter(|rp| self.ctxt.bc.same_region(*this_region, rp.region(self.ctxt)))
                .map(|mut rp| {
                    rp.label = Some(RegionProjectionLabel::Placeholder);
                    rp
                })
                .collect::<Vec<_>>();
            let result_projections: Vec<RegionProjection<MaybeOldPlace<'tcx>>> = destination
                .region_projections(self.ctxt)
                .iter()
                .filter(|rp| self.ctxt.bc.outlives(*this_region, rp.region(self.ctxt)))
                .map(|rp| (*rp).into())
                .collect();
            outputs.extend(result_projections);
            if !inputs.is_empty() && !outputs.is_empty() {
                self.record_and_apply_action(mk_create_edge_action(inputs, outputs).into())?;
            }
        }
        self.pcg
            .borrow
            .graph
            .render_debug_graph(self.ctxt, location, "final borrow_graph");
        Ok(())
    }
}

fn get_disjoint_lifetime_sets<'tcx, T: RegionProjectionBaseLike<'tcx>>(
    arg_region_projections: &[RegionProjection<'tcx, T>],
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> Vec<FxHashSet<PcgRegion>> {
    let regions = arg_region_projections
        .iter()
        .map(|rp| rp.region(ctxt))
        .collect::<FxHashSet<_>>();
    let mut disjoin_lifetime_sets: Vec<FxHashSet<PcgRegion>> = vec![];
    for region in regions.iter() {
        let candidate = disjoin_lifetime_sets
            .iter_mut()
            .find(|ls| ctxt.bc.same_region(*region, *ls.iter().next().unwrap()));
        if let Some(ls) = candidate {
            ls.insert(*region);
        } else {
            disjoin_lifetime_sets.push(FxHashSet::from_iter([*region]));
        }
    }
    disjoin_lifetime_sets
}

fn get_future_subgraph<'graph, 'mir: 'graph, 'tcx: 'mir>(
    arg_region_projections: &FxHashSet<RegionProjection<'tcx, MaybeOldPlace<'tcx>>>,
    mut source_graph: FrozenGraphRef<'graph, 'tcx>,
    ctxt: CompilerCtxt<'mir, 'tcx>,
) -> BorrowsGraph<'tcx> {
    let mut graph = BorrowsGraph::new();
    let mut queue: Vec<ExploreFrom<LocalNode<'tcx>, LocalRegionProjection<'tcx>>> =
        arg_region_projections
            .iter()
            .map(|rp| ExploreFrom::new(rp.to_local_node(ctxt), *rp))
            .collect();
    while let Some(ef) = queue.pop() {
        let blocked_by = source_graph.get_edges_blocked_by(ef.current(), ctxt);
        for edge in blocked_by.iter() {
            for node in edge.blocked_nodes(ctxt) {
                match node {
                    PCGNode::Place(_) => {
                        if let Some(local) = node.try_to_local_node(ctxt) {
                            queue.push(ef.extend(local));
                        }
                    }
                    PCGNode::RegionProjection(rp) => {
                        // RP isn't the same region, stop search
                        if !ctxt
                            .bc
                            .same_region(rp.region(ctxt), ef.connect().region(ctxt))
                        {
                            continue;
                        }

                        if rp.is_placeholder() {
                            continue;
                        }

                        // Continue search if we haven't hit a root
                        if let Some(PCGNode::RegionProjection(local_rp)) =
                            rp.try_to_local_node(ctxt)
                        {
                            if !local_rp.is_mutable(ctxt) {
                                continue;
                            }
                            // If the place is old, we can skip it but continue search up
                            if local_rp.base.is_old() {
                                queue.push(ef.extend(local_rp.into()));
                                continue;
                            }

                            // If we get here, we want to include this node

                            let future_rp = rp.label_projection(RegionProjectionLabel::Placeholder);

                            if future_rp == ef.connect().into() /* || graph.contains(future_rp, ctxt) */ {
                                // We saw, earlier, a version of the same lifetime projection at a different snapshot, lets skip for now
                                // TODO: Verify that this is correct
                                continue;
                            }

                            assert!(future_rp != ef.connect().into());

                            graph.insert(
                                BorrowPcgEdge::new(
                                    BorrowFlowEdge::new(
                                        future_rp,
                                        ef.connect(),
                                        BorrowFlowEdgeKind::FunctionCallNestedRefs,
                                        ctxt,
                                    )
                                    .into(),
                                    edge.conditions.clone(),
                                ),
                                ctxt,
                            );

                            if let Some(local @ PCGNode::RegionProjection(local_rp)) =
                                rp.try_to_local_node(ctxt)
                            {
                                queue.push(ExploreFrom::new(
                                    local,
                                    local_rp.label_projection(RegionProjectionLabel::Placeholder),
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    graph
}
