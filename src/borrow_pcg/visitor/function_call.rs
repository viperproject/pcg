use derive_more::Deref;

use super::{extract_regions, BorrowsVisitor};
use crate::{
    borrow_pcg::{
        action::BorrowPCGAction,
        borrow_pcg_edge::BorrowPCGEdge,
        coupling_graph_constructor::BorrowCheckerInterface,
        edge::abstraction::{AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction},
        path_condition::PathConditions,
        region_projection::{LocalRegionProjection, PcgRegion},
    },
    pcg::{PCGUnsupportedError, PcgError},
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::{
            mir::{Const, Location, Operand},
            ty::{self},
        },
    },
    utils::{self, maybe_old::MaybeOldPlace, CompilerCtxt, PlaceSnapshot, SnapshotLocation},
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

        let mk_create_edge_action = |input, output| {
            let edge = BorrowPCGEdge::new(
                AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                    location,
                    *func_def_id,
                    substs,
                    AbstractionBlockEdge::new(input, output),
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
                input_place.region_projections(self.ctxt)
            })
            .collect::<Vec<_>>();

        for arg in arg_region_projections.iter() {
            self.state.label_region_projection(
                arg,
                SnapshotLocation::before(location),
                self.ctxt,
            );
        }

        #[derive(Default, Deref)]
        struct CoupledRegionProjections<'tcx>(Vec<FxHashSet<LocalRegionProjection<'tcx>>>);

        impl<'tcx> CoupledRegionProjections<'tcx> {
            fn find_matching<'mir>(
                &mut self,
                region: PcgRegion,
                borrow_checker: &dyn BorrowCheckerInterface<'mir, 'tcx>,
                repacker: CompilerCtxt<'mir, 'tcx>,
            ) -> Option<&mut FxHashSet<LocalRegionProjection<'tcx>>> {
                self.0.iter_mut().find(|set| {
                    borrow_checker.same_region(region, set.iter().next().unwrap().region(repacker))
                })
            }

            fn insert<'mir>(
                &mut self,
                projection: LocalRegionProjection<'tcx>,
                borrow_checker: &dyn BorrowCheckerInterface<'mir, 'tcx>,
                repacker: CompilerCtxt<'mir, 'tcx>,
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
            coupled_region_projections.insert(*projection, self.bc.as_ref(), self.ctxt);
        }

        for coupled in coupled_region_projections.iter() {
            let create_edge_action = BorrowPCGAction::add_edge(
                BorrowPCGEdge::new(
                    AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                        location,
                        *func_def_id,
                        substs,
                        AbstractionBlockEdge::new(
                            coupled
                                .iter()
                                .map(|rp| {
                                    rp.label_projection(SnapshotLocation::before(location))
                                        .into()
                                })
                                .collect(),
                            coupled
                                .clone()
                                .into_iter()
                                .map(|rp| rp.label_projection(location.into()))
                                .collect(),
                        ),
                    ))
                    .into(),
                    PathConditions::AtBlock(location.block),
                ),
                true,
            );
            self.apply_action(create_edge_action);
        }

        for arg in args.iter() {
            let input_place: utils::Place<'tcx> = match arg.place() {
                Some(place) => place.into(),
                None => continue,
            };
            let input_place = MaybeOldPlace::OldPlace(PlaceSnapshot::new(
                input_place,
                self.state.get_latest(input_place),
            ));
            let ty = input_place.ty(self.ctxt).ty;
            for (lifetime_idx, input_lifetime) in
                extract_regions(ty, self.ctxt).into_iter_enumerated()
            {
                for output in
                    self.projections_borrowing_from_input_lifetime(input_lifetime, destination)
                {
                    let input_rp = input_place
                        .region_projection(lifetime_idx, self.ctxt)
                        .label_projection(location.into());
                    self.apply_action(mk_create_edge_action(
                        std::iter::once(input_rp.into()).collect(),
                        std::iter::once(output).collect(),
                    ));
                }
            }
        }
        Ok(())
    }
}
