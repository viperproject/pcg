use super::PcgVisitor;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPCGEdge;
use crate::borrow_pcg::domain::AbstractionInputTarget;
use crate::borrow_pcg::edge::abstraction::{
    AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction,
};
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::{
    PcgRegion, RegionProjection, RegionProjectionBaseLike, RegionProjectionLabel,
};
use crate::rustc_interface::middle::mir::{Location, Operand};

use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::rustc_interface::middle::ty::{self};
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{self, CompilerCtxt, PlaceSnapshot, SnapshotLocation};

use super::PcgError;

impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(super) fn make_function_call_abstraction(
        &mut self,
        func: &Operand<'tcx>,
        args: &[&Operand<'tcx>],
        destination: utils::Place<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        // This is just a performance optimization
        if self
            .pcg
            .borrow
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
                    self.pcg.borrow.get_latest(input_place),
                ));
                input_place.region_projections(self.ctxt)
            })
            .collect::<Vec<_>>();

        let mut labelled_rps = FxHashSet::default();
        for arg in arg_region_projections.iter() {
            if arg.is_nested_in_local_ty(self.ctxt) {
                self.pcg.borrow.label_region_projection(
                    arg,
                    Some(SnapshotLocation::before(location).into()),
                    self.ctxt,
                );
                labelled_rps
                    .insert(arg.label_projection(SnapshotLocation::before(location).into()));
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

        let source_arg_projections = arg_region_projections
            .iter()
            .map(|rp| {
                if rp.is_nested_in_local_ty(self.ctxt) {
                    (*rp).label_projection(SnapshotLocation::before(location).into())
                } else {
                    *rp
                }
            })
            .collect::<Vec<_>>();

        let disjoint_lifetime_sets = get_disjoint_lifetime_sets(&arg_region_projections, self.ctxt);
        for ls in disjoint_lifetime_sets.iter() {
            let this_region = ls.iter().next().unwrap();
            let inputs: Vec<AbstractionInputTarget<'tcx>> = source_arg_projections
                .iter()
                .filter(|rp| self.ctxt.bc.outlives(rp.region(self.ctxt), *this_region))
                .map(|rp| (*rp).into())
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
