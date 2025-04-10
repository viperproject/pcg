use super::{extract_regions, BorrowsVisitor};
use crate::{
    borrow_pcg::{
        action::BorrowPCGAction,
        borrow_pcg_edge::BorrowPCGEdge,
        edge::abstraction::{AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction},
        path_condition::PathConditions,
    },
    pcg::PcgError,
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::{
            mir::{Location, Operand},
            ty::{self},
        },
    },
    utils::{self, maybe_old::MaybeOldPlace, PlaceSnapshot, SnapshotLocation},
};

impl<'tcx> BorrowsVisitor<'tcx, '_, '_,> {
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
        let func_ty = func.ty(self.ctxt.body(), self.ctxt.tcx());
        let (func_def_id, substs) = if let ty::TyKind::FnDef(def_id, substs) = func_ty.kind() {
            (def_id, substs)
        } else {
            panic!("Expected a function definition");
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
            self.state
                .label_region_projection(arg, SnapshotLocation::before(location), self.ctxt);
        }

        let regions = arg_region_projections
            .iter()
            .map(|rp| rp.region(self.ctxt))
            .collect::<FxHashSet<_>>();

        for region in regions.iter() {
            let inputs = arg_region_projections
                .iter()
                .filter(|rp| self.ctxt.bc.same_region(*region, rp.region(self.ctxt)))
                .map(|rp| {
                    (*rp)
                        .label_projection(SnapshotLocation::before(location))
                        .into()
                })
                .collect::<Vec<_>>();
            let outputs = arg_region_projections
                .iter()
                .filter(|rp| self.ctxt.bc.same_region(*region, rp.region(self.ctxt)))
                .map(|rp| (*rp).label_projection(SnapshotLocation::After(location)))
                .collect::<Vec<_>>();
            self.apply_action(mk_create_edge_action(inputs, outputs));
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
                for output in self.projections_borrowing_from_input_lifetime(
                    input_lifetime,
                    destination
                ) {
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
