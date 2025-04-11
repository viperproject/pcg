use super::{extract_regions, BorrowsVisitor};
use crate::{
    borrow_pcg::{
        action::BorrowPCGAction,
        borrow_pcg_edge::BorrowPCGEdge,
        edge::abstraction::{AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction},
        path_condition::PathConditions,
        region_projection::{RegionProjection, RegionProjectionLabel},
    },
    pcg::PcgError,
    rustc_interface::{
        data_structures::fx::{FxHashMap, FxHashSet},
        middle::{
            mir::{Location, Operand},
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

        let mut labelled_rps = FxHashSet::default();
        for arg in arg_region_projections.iter() {
            if arg.is_nested_in_local_ty(self.ctxt) {
                self.state.label_region_projection(
                    arg,
                    SnapshotLocation::before(location).into(),
                    self.ctxt,
                );
                labelled_rps
                    .insert(arg.label_projection(SnapshotLocation::before(location).into()));
            }
        }
        let regions = arg_region_projections
            .iter()
            .map(|rp| rp.region(self.ctxt))
            .collect::<FxHashSet<_>>();

        let placeholder_targets = labelled_rps
            .iter()
            .flat_map(|rp| {
                self.state
                    .graph()
                    .identify_placeholder_target((*rp).into(), self.ctxt)
            })
            .collect::<FxHashSet<_>>();

        for region in regions.iter() {
            let inputs = arg_region_projections
                .iter()
                .filter(|rp| self.ctxt.bc.same_region(*region, rp.region(self.ctxt)))
                .map(|rp| {
                    if rp.is_nested_in_local_ty(self.ctxt) {
                        (*rp)
                            .label_projection(SnapshotLocation::before(location).into())
                            .into()
                    } else {
                        (*rp).into()
                    }
                })
                .collect::<Vec<_>>();
            let outputs = placeholder_targets
                .iter()
                .copied()
                .filter(|rp| {
                    rp.is_nested_in_local_ty(self.ctxt)
                        && self.ctxt.bc.same_region(*region, rp.region(self.ctxt))
                })
                .map(|mut rp| {
                    rp.label = Some(RegionProjectionLabel::Placeholder);
                    rp
                })
                .collect::<Vec<_>>();
            if !inputs.is_empty() && !outputs.is_empty() {
                self.apply_action(mk_create_edge_action(inputs, outputs));
            }
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
