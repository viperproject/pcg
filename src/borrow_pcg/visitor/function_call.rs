use super::BorrowsVisitor;
use crate::{
    borrow_pcg::{
        action::BorrowPCGAction,
        borrow_pcg_edge::BorrowPCGEdge,
        edge::abstraction::{AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction},
        path_condition::PathConditions,
        region_projection::{
            HasRegionProjections, PcgRegion, RegionProjection, RegionProjectionBaseLike,
            RegionProjectionLabel,
        },
    },
    pcg::PcgError,
    rustc_interface::{
        data_structures::fx::FxHashSet,
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
                self.state
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

        let disjoin_lifetime_sets = get_disjoint_lifetime_sets(&arg_region_projections, self.ctxt);
        for ls in disjoin_lifetime_sets.iter() {
            let this_region = ls.iter().next().unwrap();
            let inputs = source_arg_projections
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
                self.apply_action(mk_create_edge_action(inputs, outputs));
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
