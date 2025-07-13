use super::PcgVisitor;
use crate::action::BorrowPcgAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdge;
use crate::borrow_pcg::domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput};
use crate::borrow_pcg::edge::abstraction::function::{FunctionCallAbstraction, FunctionData};
use crate::borrow_pcg::edge::abstraction::{AbstractionBlockEdge, AbstractionType};
use crate::borrow_pcg::region_projection::RegionProjectionLabel;
use crate::rustc_interface::middle::mir::{Location, Operand};
use crate::utils::display::DisplayWithCompilerCtxt;

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
        // TODO: Check whether this logic makes sense
        // for arg in args.iter() {
        //     if let Some(arg_place) = arg.place() {
        //         let arg_place: utils::Place<'tcx> = arg_place.into();
        //         if arg_place
        //             .iter_places(self.ctxt)
        //             .iter()
        //             .any(|p| p.is_raw_ptr(self.ctxt))
        //         {
        //             return Err(PcgError::unsupported(
        //                 PCGUnsupportedError::FunctionCallWithUnsafePtrArgument,
        //             ));
        //         }
        //     }
        // }
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
        let ctxt = self.ctxt;

        let mk_create_edge_action =
            |input: FunctionCallAbstractionInput<'tcx>, output, context: &str| {
                let edge = BorrowPcgEdge::new(
                    AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                        location,
                        function_data,
                        AbstractionBlockEdge::new(vec![input], output, ctxt),
                    ))
                    .into(),
                    path_conditions.clone(),
                );
                BorrowPcgAction::add_edge(edge, context, false)
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
                    self.pcg.borrow.get_latest(input_place, self.ctxt),
                ));
                input_place.region_projections(self.ctxt)
            })
            .collect::<Vec<_>>();

        // The subset of the argument region projections that are nested
        // (and labelled, since the set of borrows inside may be modified)
        let mut labelled_rps = FxHashSet::default();
        for arg in arg_region_projections.iter() {
            if arg.is_invariant_in_type(self.ctxt) {
                self.record_and_apply_action(
                    BorrowPcgAction::label_region_projection(
                        *arg,
                        Some(SnapshotLocation::before(location).into()),
                        format!(
                            "Function call: {} is invariant in type {:?}; therefore it will be labelled as the set of borrows inside may be modified",
                            arg.to_short_string(self.ctxt),
                            arg.base.ty(self.ctxt).ty,
                        ),
                    )
                    .into(),
                )?;
                labelled_rps.insert(
                    arg.with_label(Some(SnapshotLocation::before(location).into()), self.ctxt),
                );
            }
        }

        let placeholder_targets = labelled_rps
            .iter()
            .flat_map(|rp| {
                self.pcg
                    .borrow
                    .graph()
                    .identify_placeholder_target(*rp, self.ctxt)
            })
            .collect::<FxHashSet<_>>();

        // The set of region projections that contain borrows that could be
        // moved into the labelled rps (as they are seen after the function call)
        let source_arg_projections = arg_region_projections
            .iter()
            .map(|rp| {
                if rp.is_invariant_in_type(self.ctxt) {
                    (*rp).with_label(Some(SnapshotLocation::before(location).into()), self.ctxt)
                } else {
                    *rp
                }
            })
            .collect::<Vec<_>>();

        for arg_rp in source_arg_projections {
            let this_region = arg_rp.region(self.ctxt);
            let mut outputs = placeholder_targets
                .iter()
                .copied()
                .filter(|rp| self.ctxt.bc.same_region(this_region, rp.region(self.ctxt)))
                .map(|rp| {
                    FunctionCallAbstractionOutput::new(
                        rp.with_label(Some(RegionProjectionLabel::Placeholder), self.ctxt),
                    )
                })
                .collect::<Vec<_>>();
            let result_projections: Vec<FunctionCallAbstractionOutput<'tcx>> = destination
                .region_projections(self.ctxt)
                .iter()
                .filter(|rp| self.ctxt.bc.outlives(this_region, rp.region(self.ctxt)))
                .map(|rp| (*rp).into())
                .collect();
            outputs.extend(result_projections);
            if !outputs.is_empty() {
                self.record_and_apply_action(
                    mk_create_edge_action(
                        arg_rp.into(),
                        outputs,
                        "Function call: edges for nested borrows",
                    )
                    .into(),
                )?;
            }
        }
        // self.pcg.render_debug_graph(self.ctxt, location, "final borrow_graph");
        Ok(())
    }
}
