use super::PcgError;
use super::PcgVisitor;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPCGEdge;
use crate::borrow_pcg::domain::AbstractionInputTarget;
use crate::borrow_pcg::edge::abstraction::{
    AbstractionBlockEdge, AbstractionType, FnDefData, FnPtrData, FunctionCallAbstraction,
    FunctionData,
};
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::{
    HasRegionProjections, HasRegions, PcgRegion, RegionProjection, RegionProjectionBaseLike,
    RegionProjectionLabel, TyRegion,
};
use crate::rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};
use crate::rustc_interface::middle::ty::{self, ProjectionPredicate, TraitPredicate, Ty};
use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::mir::{Location, Operand},
};
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{self, CompilerCtxt, PlaceSnapshot, SnapshotLocation};

#[derive(Clone, Default, Debug)]
struct TyConstraints<'tcx> {
    trait_predicates: FxHashSet<TraitPredicate<'tcx>>,
    region_outlives: FxHashSet<TyRegion>,
    projection_predicates: FxHashSet<ProjectionPredicate<'tcx>>,
}

#[derive(Clone, Default, Debug)]
struct TyRegionCtxt<'tcx> {
    type_constraints: FxHashMap<Ty<'tcx>, TyConstraints<'tcx>>,
    region_outlives: FxHashMap<TyRegion, FxHashSet<TyRegion>>,
    place_ty_map: FxHashMap<utils::Place<'tcx>, Ty<'tcx>>,
    inputs_region_map: FxHashMap<TyRegion, PcgRegion>,
    output_region_map: FxHashMap<TyRegion, PcgRegion>,
}

impl<'tcx> TyRegionCtxt<'tcx> {
    fn new(
        repacker: CompilerCtxt<'_, 'tcx>,
        function_data: FunctionData<'tcx>,
        arg_places: Vec<utils::Place<'tcx>>,
        destination: &utils::Place<'tcx>,
    ) -> Self {
        let mut ty_region_ctxt = Self::default();
        match function_data {
            FunctionData::FnDefData(fn_def_data) => {
                ty_region_ctxt.infer_constraints(repacker, fn_def_data.def_id());
                let (output, inputs) = fn_def_data.inputs_and_output().split_last().unwrap();
                ty_region_ctxt.infer_mappings(repacker, arg_places, destination, inputs, output);
            }
            FunctionData::FnPtrData(fn_ptr_data) => {
                let (output, inputs) = fn_ptr_data.inputs_and_output().split_last().unwrap();
                ty_region_ctxt.infer_mappings(repacker, arg_places, destination, inputs, output);
            }
        };
        ty_region_ctxt
    }

    fn infer_constraints(&mut self, repacker: CompilerCtxt<'_, 'tcx>, def_id: DefId) {
        for (clause, _span) in repacker.tcx().predicates_of(def_id).predicates {
            match clause.kind().skip_binder() {
                ty::ClauseKind::Trait(trait_predicate) => {
                    let ty = trait_predicate.self_ty();
                    if let Some(ty_constraints) = self.type_constraints.get_mut(&ty) {
                        ty_constraints.trait_predicates.insert(trait_predicate);
                    } else {
                        let mut ty_constraints = TyConstraints::default();
                        ty_constraints.trait_predicates.insert(trait_predicate);
                        self.type_constraints.insert(ty, ty_constraints);
                    }
                }
                ty::ClauseKind::RegionOutlives(outlives_predicate) => {
                    let sup = outlives_predicate.0.into();
                    let sub = outlives_predicate.1.into();
                    if let Some(ty_regions) = self.region_outlives.get_mut(&sup) {
                        ty_regions.insert(sub);
                    } else {
                        let mut ty_regions = FxHashSet::default();
                        ty_regions.insert(sub);
                        self.region_outlives.insert(sup, ty_regions);
                    }
                }
                ty::ClauseKind::TypeOutlives(outlives_predicate) => {
                    let sup = outlives_predicate.0.into();
                    let sub = outlives_predicate.1.into();
                    if let Some(ty_constraints) = self.type_constraints.get_mut(&sup) {
                        ty_constraints.region_outlives.insert(sub);
                    } else {
                        let mut ty_constraints = TyConstraints::default();
                        ty_constraints.region_outlives.insert(sub);
                        self.type_constraints.insert(sup, ty_constraints);
                    }
                }
                ty::ClauseKind::Projection(projection_predicate) => {
                    let ty = projection_predicate.self_ty();
                    if let Some(ty_constraints) = self.type_constraints.get_mut(&ty) {
                        ty_constraints
                            .projection_predicates
                            .insert(projection_predicate);
                    } else {
                        let mut ty_constraints = TyConstraints::default();
                        ty_constraints
                            .projection_predicates
                            .insert(projection_predicate);
                        self.type_constraints.insert(ty, ty_constraints);
                    }
                }
                // unused clause kinds
                // ty::ClauseKind::ConstArgHasType(_, _) => todo!(),
                // ty::ClauseKind::WellFormed(_) => todo!(),
                // ty::ClauseKind::ConstEvaluatable(_) => todo!(),
                // ty::ClauseKind::HostEffect(host_effect_predicate) => todo!(),
                _ => {} // do nothing
            }
        }
    }

    fn infer_mappings(
        &mut self,
        repacker: CompilerCtxt<'_, 'tcx>,
        arg_places: Vec<utils::Place<'tcx>>,
        destination: &utils::Place<'tcx>,
        inputs: &[Ty<'tcx>],
        output: &Ty<'tcx>,
    ) {
        for (place, ty) in arg_places.iter().zip(inputs) {
            self.place_ty_map.insert(*place, *ty);
        }

        for (ty, place) in self.place_ty_map.iter().flat_map(|(place, ty)| {
            let ty_regions = ty.regions(repacker);
            let pcg_regions = place.regions(repacker);
            ty_regions.into_iter().zip(pcg_regions.into_iter())
        }) {
            self.inputs_region_map.insert(ty, place);
        }

        for (ty, place) in output
            .regions(repacker)
            .into_iter()
            .zip(destination.regions(repacker).into_iter())
        {
            self.output_region_map.insert(ty, place);
        }

        self.place_ty_map.insert(*destination, *output);
    }

    fn equivalent(
        &self,
        repacker: CompilerCtxt<'_, 'tcx>,
        ty_region_projection: RegionProjection<'tcx, Ty<'tcx>, TyRegion>,
        pcg_region_projection: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        is_input: bool,
    ) -> bool {
        let mapping = if is_input {
            &self.inputs_region_map
        } else {
            &self.output_region_map
        };

        let place = match pcg_region_projection.base {
            MaybeOldPlace::Current { place } => place,
            MaybeOldPlace::OldPlace(place_snapshot) => place_snapshot.place,
        };
        self.place_ty_map
            .get(&place)
            .is_some_and(|ty| *ty == ty_region_projection.base)
            && mapping
                .get(&ty_region_projection.region(repacker))
                .is_some_and(|pcg_region| *pcg_region == pcg_region_projection.region(repacker))
    }

    fn outlives(&self, repacker: CompilerCtxt<'_, 'tcx>, sup: TyRegion, sub: TyRegion) -> bool {
        match (sup, sub) {
            // this case generally shouldn't happen since these aren't concrete types
            (TyRegion::RegionVid(sup_region), TyRegion::RegionVid(sub_region)) => repacker
                .bc
                .region_infer_ctxt()
                .eval_outlives(sup_region, sub_region),
            (TyRegion::ReStatic, _) => true,
            // region outlives relations should be a DAG, dfs to check
            (_, _) => {
                sup == sub
                    || self.region_outlives.get(&sup).map_or(false, |regions| {
                        regions
                            .iter()
                            .any(|&region| self.outlives(repacker, region, sub))
                    })
            }
        }
    }

    fn same_region(
        &self,
        repacker: CompilerCtxt<'_, 'tcx>,
        reg1: TyRegion,
        reg2: TyRegion,
    ) -> bool {
        self.outlives(repacker, reg1, reg2) && self.outlives(repacker, reg2, reg1)
    }
}

fn get_function_data<'tcx>(
    func: &Operand<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> FunctionData<'tcx> {
    match func.ty(ctxt.body(), ctxt.tcx()).kind() {
        ty::TyKind::FnDef(def_id, substs) => {
            FunctionData::FnDefData(FnDefData::new(ctxt, *def_id, substs))
        }
        ty::TyKind::FnPtr(binder, _) => {
            FunctionData::FnPtrData(FnPtrData::new(binder.skip_binder()))
        }
        _ => panic!("shouldn't be passed here"),
    }
}

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

        let function_data = get_function_data(func, self.ctxt);
        let function_in_out = function_data.inputs_and_output();

        let inputs = function_in_out.split_last().unwrap().1;
        let output = function_in_out.split_last().unwrap().0;

        assert!(args.len() == inputs.len());

        let ty_region_ctxt = TyRegionCtxt::new(
            self.ctxt,
            function_data,
            args.iter()
                .map(|arg| arg.place().unwrap().into())
                .collect::<Vec<_>>(),
            &destination,
        );

        let mk_create_edge_action = |input, output| {
            let edge = BorrowPCGEdge::new(
                AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                    location,
                    function_data,
                    AbstractionBlockEdge::new(input, output),
                ))
                .into(),
                PathConditions::AtBlock(location.block),
            );
            BorrowPCGAction::add_edge(edge, true)
        };

        // region projections

        let param_region_projections = inputs
            .iter()
            .flat_map(|&ty| ty.region_projections(self.ctxt))
            .collect::<Vec<_>>();

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

        // labelled rps

        let mut labelled_param_rps = FxHashSet::default();
        for rp in param_region_projections.iter() {
            if rp.is_nested_in_local_ty(self.ctxt) {
                labelled_param_rps
                    .insert(rp.label_projection(SnapshotLocation::before(location).into()));
            }
        }

        let mut labelled_arg_rps = FxHashSet::default();
        for rp in arg_region_projections.iter() {
            if rp.is_nested_in_local_ty(self.ctxt) {
                self.pcg.borrow.label_region_projection(
                    rp,
                    Some(SnapshotLocation::before(location).into()),
                    self.ctxt,
                );
                labelled_arg_rps
                    .insert(rp.label_projection(SnapshotLocation::before(location).into()));
            }
        }

        // placeholder targets

        let param_placeholder_targets: FxHashSet<RegionProjection<'_, Ty<'_>, TyRegion>> =
            FxHashSet::default();

        let arg_placeholder_targets = labelled_arg_rps
            .iter()
            .flat_map(|rp| {
                self.pcg
                    .borrow
                    .graph()
                    .identify_placeholder_target(*rp, self.ctxt)
            })
            .collect::<FxHashSet<_>>();

        // source projections

        let source_param_projections = param_region_projections
            .iter()
            .map(|rp| {
                if rp.is_nested_in_local_ty(self.ctxt) {
                    (*rp).label_projection(SnapshotLocation::before(location).into())
                } else {
                    *rp
                }
            })
            .collect::<Vec<_>>();

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

        // disjoint lifetime sets

        let disjoint_param_lifetime_sets = get_disjoint_param_lifetime_sets(
            &param_region_projections,
            self.ctxt,
            ty_region_ctxt.clone(),
        );

        let _disjoint_arg_lifetime_sets =
            get_disjoint_arg_lifetime_sets(&arg_region_projections, self.ctxt);

        // for ls in disjoint_arg_lifetime_sets.iter() {
        //     let this_region = ls.iter().next().unwrap();
        //     let _inputs: Vec<AbstractionInputTarget<'tcx>> = source_arg_projections
        //         .iter()
        //         .filter(|rp| self.ctxt.bc.outlives(rp.region(self.ctxt), *this_region))
        //         .map(|rp| (*rp).into())
        //         .collect::<Vec<_>>();
        //     let mut outputs = arg_placeholder_targets
        //         .iter()
        //         .copied()
        //         .filter(|rp| self.ctxt.bc.same_region(*this_region, rp.region(self.ctxt)))
        //         .map(|mut rp| {
        //             rp.label = Some(RegionProjectionLabel::Placeholder);
        //             rp
        //         })
        //         .collect::<Vec<_>>();
        //     let result_projections: Vec<RegionProjection<MaybeOldPlace<'tcx>>> = destination
        //         .region_projections(self.ctxt)
        //         .iter()
        //         .filter(|rp| self.ctxt.bc.outlives(*this_region, rp.region(self.ctxt)))
        //         .map(|rp| (*rp).into())
        //         .collect();
        //     outputs.extend(result_projections);
        //     if !inputs.is_empty() && !outputs.is_empty() {
        //         self.record_and_apply_action(mk_create_edge_action(inputs, outputs).into())?;
        //     }
        // }

        let dest_rps = destination.region_projections(self.ctxt);

        for ls in disjoint_param_lifetime_sets.iter() {
            let this_region = ls.iter().next().unwrap();
            let inputs: Vec<AbstractionInputTarget<'tcx>> = source_param_projections
                .iter()
                .filter(|rp| ty_region_ctxt.outlives(self.ctxt, rp.region(self.ctxt), *this_region))
                .filter_map(|ty_rp| {
                    source_arg_projections
                        .iter()
                        .find(|&pcg_rp| ty_region_ctxt.equivalent(self.ctxt, *ty_rp, *pcg_rp, true))
                })
                .map(|rp| (*rp).into())
                .collect::<Vec<_>>();
            let mut outputs = param_placeholder_targets
                .iter()
                .copied()
                .filter(|rp| ty_region_ctxt.outlives(self.ctxt, *this_region, rp.region(self.ctxt)))
                .filter_map(|ty_rp| {
                    arg_placeholder_targets
                        .iter()
                        .find(|&pcg_rp| ty_region_ctxt.equivalent(self.ctxt, ty_rp, *pcg_rp, false))
                        .map(|rp| *rp)
                })
                .map(|mut rp| {
                    rp.label = Some(RegionProjectionLabel::Placeholder);
                    rp.into()
                })
                .collect::<Vec<_>>();
            let result_projections: Vec<RegionProjection<MaybeOldPlace<'tcx>>> = output
                .region_projections(self.ctxt)
                .iter()
                .filter(|rp| ty_region_ctxt.outlives(self.ctxt, *this_region, rp.region(self.ctxt)))
                .filter_map(|ty_rp| {
                    dest_rps.iter().find(|&pcg_rp| {
                        ty_region_ctxt.equivalent(self.ctxt, *ty_rp, (*pcg_rp).into(), false)
                    })
                })
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

fn get_disjoint_param_lifetime_sets<'tcx>(
    param_region_projections: &[RegionProjection<'tcx, Ty<'tcx>, TyRegion>],
    ctxt: CompilerCtxt<'_, 'tcx>,
    ty_region_ctxt: TyRegionCtxt<'tcx>,
) -> Vec<FxHashSet<TyRegion>> {
    let regions = param_region_projections
        .iter()
        .map(|rp| rp.region(ctxt))
        .collect::<FxHashSet<_>>();
    let mut disjoint_lifetime_sets: Vec<FxHashSet<TyRegion>> = vec![];
    for region in regions.iter() {
        let candidate = disjoint_lifetime_sets
            .iter_mut()
            .find(|ls| ty_region_ctxt.same_region(ctxt, *region, *ls.iter().next().unwrap()));
        if let Some(ls) = candidate {
            ls.insert(*region);
        } else {
            disjoint_lifetime_sets.push(FxHashSet::from_iter([*region]));
        }
    }
    disjoint_lifetime_sets
}

fn get_disjoint_arg_lifetime_sets<'tcx, T: RegionProjectionBaseLike<'tcx>>(
    arg_region_projections: &[RegionProjection<'tcx, T>],
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> Vec<FxHashSet<PcgRegion>> {
    let regions = arg_region_projections
        .iter()
        .map(|rp| rp.region(ctxt))
        .collect::<FxHashSet<_>>();
    let mut disjoint_lifetime_sets: Vec<FxHashSet<PcgRegion>> = vec![];
    for region in regions.iter() {
        let candidate = disjoint_lifetime_sets
            .iter_mut()
            .find(|ls| ctxt.bc.same_region(*region, *ls.iter().next().unwrap()));
        if let Some(ls) = candidate {
            ls.insert(*region);
        } else {
            disjoint_lifetime_sets.push(FxHashSet::from_iter([*region]));
        }
    }
    disjoint_lifetime_sets
}
