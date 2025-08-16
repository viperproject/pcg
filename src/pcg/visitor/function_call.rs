use super::PcgVisitor;
use crate::action::BorrowPcgAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdge;
use crate::borrow_pcg::domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput};
use crate::borrow_pcg::edge::abstraction::function::{FunctionCallAbstraction, FunctionData};
use crate::borrow_pcg::edge::abstraction::{AbstractionBlockEdge, AbstractionType};
use crate::borrow_pcg::has_pcs_elem::LabelLifetimeProjectionPredicate;
use crate::pcg::obtain::{HasSnapshotLocation, PlaceExpander};
use crate::rustc_interface::middle::mir::{Location, Operand};
use crate::utils::display::DisplayWithCompilerCtxt;

use super::PcgError;
use crate::rustc_interface::middle::ty::{self};
use crate::utils::{self, DataflowCtxt, HasCompilerCtxt, SnapshotLocation};

fn get_function_data<'a, 'tcx: 'a>(
    func: &Operand<'tcx>,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> Option<FunctionData<'tcx>> {
    match func.ty(ctxt.body(), ctxt.tcx()).kind() {
        ty::TyKind::FnDef(def_id, substs) => Some(FunctionData::new(*def_id, substs)),
        ty::TyKind::FnPtr(..) => None,
        _ => None,
    }
}

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    #[tracing::instrument(skip(self, func, args, destination))]
    pub(super) fn make_function_call_abstraction(
        &mut self,
        func: &Operand<'tcx>,
        args: &[&Operand<'tcx>],
        destination: utils::Place<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        let function_data = get_function_data(func, self.ctxt);

        let path_conditions = self.pcg.borrow.validity_conditions.clone();
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
                BorrowPcgAction::add_edge(edge, context, ctxt)
            };

        // The versions of the region projections for the function inputs just
        // before they were moved out, labelled with their last modification
        // time
        let arg_region_projections = args
            .iter()
            .filter_map(|arg| self.maybe_labelled_operand_place(arg))
            .flat_map(|input_place| input_place.lifetime_projections(self.ctxt))
            .collect::<Vec<_>>();

        let pre_rps = arg_region_projections
            .iter()
            .map(|rp| {
                rp.with_label(
                    Some(self.place_obtainer().prev_snapshot_location().into()),
                    self.ctxt,
                )
            })
            .collect::<Vec<_>>();

        let post_rps = arg_region_projections
            .iter()
            .map(|rp| {
                rp.with_label(
                    Some(SnapshotLocation::After(self.location().block).into()),
                    self.ctxt,
                )
            })
            .collect::<Vec<_>>();

        for (rp, post_rp) in arg_region_projections.iter().zip(post_rps.iter()) {
            self.place_obtainer()
                .redirect_source_of_future_edges(*rp, *post_rp, ctxt)?;
        }

        for (rp, pre_rp) in arg_region_projections.iter().zip(pre_rps.iter()) {
            self.record_and_apply_action(
                BorrowPcgAction::label_lifetime_projection(
                    LabelLifetimeProjectionPredicate::Equals(*rp),
                    pre_rp.label(),
                    format!(
                        "Function call:Label Pre version of {}",
                        rp.to_short_string(self.ctxt.bc_ctxt()),
                    ),
                )
                .into(),
            )?;
        }

        for pre_rp in pre_rps {
            let mut outputs = vec![];
            for post_rp in post_rps.iter() {
                if post_rp.is_invariant_in_type(self.ctxt)
                    && self.ctxt.bc_ctxt().bc.outlives(
                        pre_rp.region(self.ctxt),
                        post_rp.region(self.ctxt),
                        location,
                    )
                {
                    outputs.push((*post_rp).into());
                }
            }
            let result_projections: Vec<FunctionCallAbstractionOutput<'tcx>> = destination
                .lifetime_projections(self.ctxt)
                .iter()
                .filter(|rp| {
                    self.ctxt.bc().outlives(
                        pre_rp.region(self.ctxt),
                        rp.region(self.ctxt),
                        location,
                    )
                })
                .map(|rp| (*rp).into())
                .collect();
            outputs.extend(result_projections);
            if !outputs.is_empty() {
                self.record_and_apply_action(
                    mk_create_edge_action(pre_rp.into(), outputs, "Function call").into(),
                )?;
            }
        }

        Ok(())
    }
}
