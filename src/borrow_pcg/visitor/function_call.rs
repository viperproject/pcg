use derive_more::Deref;

use super::{extract_regions, BorrowsVisitor};
use crate::{
    borrow_pcg::{
        action::BorrowPCGAction,
        borrow_pcg_edge::BorrowPCGEdge,
        coupling_graph_constructor::BorrowCheckerInterface,
        domain::{AbstractionInputTarget, AbstractionOutputTarget},
        edge::{
            abstraction::{AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction},
            coupling::FunctionCallRegionCoupling,
            outlives::{OutlivesEdge, OutlivesEdgeKind},
        },
        path_condition::PathConditions,
        region_projection::{LocalRegionProjection, PCGRegion},
    },
    combined_pcs::{PCGUnsupportedError, PcgError},
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::{
            mir::{Const, Location, Operand},
            ty::{self},
        },
    },
    utils::{self, maybe_old::MaybeOldPlace, PlaceRepacker, PlaceSnapshot},
};

impl<'tcx> BorrowsVisitor<'tcx, '_, '_> {
    /// Constructs a function call abstraction, if necessary.
    pub(super) fn make_function_call_abstraction(
        &mut self,
        func: &Operand<'tcx>,
        args: &[&Operand<'tcx>],
        destination: utils::Place<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        // This is just a performance optimization
        if self
            .state
            .graph()
            .has_function_call_abstraction_at(location)
        {
            return Ok(());
        }
        let (func_def_id, substs) = if let Operand::Constant(box c) = func
            && let Const::Val(_, ty) = c.const_
            && let ty::TyKind::FnDef(def_id, substs) = ty.kind()
        {
            (def_id, substs)
        } else {
            return Err(PcgError::unsupported(PCGUnsupportedError::ClosureCall));
        };

        let mk_create_edge_action =
            |input: AbstractionInputTarget<'tcx>, output: AbstractionOutputTarget<'tcx>| {
                let edge = BorrowPCGEdge::new(
                    AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                        location,
                        *func_def_id,
                        substs,
                        AbstractionBlockEdge::new(
                            vec![input].into_iter().collect(),
                            vec![output].into_iter().collect(),
                        ),
                    ))
                    .into(),
                    PathConditions::AtBlock(location.block),
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
                    self.state.get_latest(input_place),
                ));
                input_place.region_projections(self.repacker)
            })
            .collect::<Vec<_>>();

        #[derive(Default, Deref)]
        struct CoupledRegionProjections<'tcx>(Vec<FxHashSet<LocalRegionProjection<'tcx>>>);

        impl<'tcx> CoupledRegionProjections<'tcx> {
            fn find_matching<'mir>(
                &mut self,
                region: PCGRegion,
                borrow_checker: &dyn BorrowCheckerInterface<'mir, 'tcx>,
                repacker: PlaceRepacker<'mir, 'tcx>,
            ) -> Option<&mut FxHashSet<LocalRegionProjection<'tcx>>> {
                self.0.iter_mut().find(|set| {
                    set.iter()
                        .any(|rp| borrow_checker.same_region(rp.region(repacker), region))
                })
            }

            fn insert<'mir>(
                &mut self,
                projection: LocalRegionProjection<'tcx>,
                borrow_checker: &dyn BorrowCheckerInterface<'mir, 'tcx>,
                repacker: PlaceRepacker<'mir, 'tcx>,
            ) {
                if let Some(set) =
                    self.find_matching(projection.region(repacker), borrow_checker, repacker)
                {
                    set.insert(projection);
                } else {
                    self.0.push(vec![projection].into_iter().collect());
                }
            }
        }

        let mut coupled_region_projections = CoupledRegionProjections::default();

        for projection in arg_region_projections.iter() {
            coupled_region_projections.insert(*projection, self.bc.as_ref(), self.repacker);
        }

        for coupled in coupled_region_projections.iter() {
            let create_edge_action = BorrowPCGAction::add_edge(
                BorrowPCGEdge::new(
                    FunctionCallRegionCoupling::new(
                        coupled.clone(),
                        coupled
                            .iter()
                            .map(|rp| rp.labelled(location.into()))
                            .collect(),
                    )
                    .into(),
                    PathConditions::AtBlock(location.block),
                ),
                true,
            );
            self.apply_action(create_edge_action);
        }

        for coupled in coupled_region_projections.0.into_iter() {
            if coupled.len() > 1 {
                let coupled_lifetime_roots = self.state.frozen_graph().coupled_lifetime_roots(
                    coupled,
                    self.bc.as_ref(),
                    self.repacker,
                );
                for (node, to_connect) in coupled_lifetime_roots.connections_to_create().iter() {
                    for parent in to_connect.iter() {
                        let action = BorrowPCGAction::add_edge(
                            BorrowPCGEdge::new(
                                OutlivesEdge::new(
                                    *parent,
                                    *node,
                                    OutlivesEdgeKind::HavocRegion,
                                    self.repacker,
                                )
                                .into(),
                                PathConditions::AtBlock(location.block),
                            ),
                            true,
                        );
                        self.apply_action(action);
                    }
                }
            }
        }

        for arg in args.iter() {
            let input_place: utils::Place<'tcx> = match arg.place() {
                Some(place) => place.into(),
                None => continue,
            };
            let input_place = MaybeOldPlace::OldPlace(PlaceSnapshot::new(input_place, location));
            let ty = input_place.ty(self.repacker).ty;
            for (lifetime_idx, input_lifetime) in
                extract_regions(ty, self.repacker).into_iter_enumerated()
            {
                for output in
                    self.projections_borrowing_from_input_lifetime(input_lifetime, destination)
                {
                    let input_rp = input_place.region_projection(lifetime_idx, self.repacker);
                    self.apply_action(mk_create_edge_action(input_rp.into(), output));
                }
            }
        }
        Ok(())
    }
}
