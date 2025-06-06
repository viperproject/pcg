use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BlockedNode,
        has_pcs_elem::{default_make_place_old, LabelRegionProjection, MakePlaceOld},
        latest::Latest,
        region_projection::{MaybeRemoteRegionProjectionBase, RegionProjectionLabel},
    },
    edgedata_enum,
    rustc_interface::{
        data_structures::fx::{FxHashMap, FxHashSet},
        hir::def_id::DefId,
        infer::infer::{self},
        middle::{
            mir::{BasicBlock, Location},
            ty::{
                self, FnSig, FnSigTys, GenericArg, GenericArgsRef, PseudoCanonicalInput, Ty,
                TyCtxt, TypeFoldable, TypeFolder, TypeSuperFoldable, TypeVisitableExt,
            },
        },
    },
    utils::{redirect::MaybeRedirected, Place},
};

use crate::borrow_pcg::borrow_pcg_edge::{BorrowPCGEdge, LocalNode, ToBorrowsEdge};
use crate::borrow_pcg::domain::{AbstractionInputTarget, AbstractionOutputTarget};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::has_pcs_elem::HasPcgElems;
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::pcg::{LocalNodeLike, PCGNode};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::CompilerCtxt;
use itertools::Itertools;
use smallvec::SmallVec;

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct LoopAbstraction<'tcx> {
    pub(crate) edge: AbstractionBlockEdge<'tcx>,
    pub(crate) block: BasicBlock,
}

impl<'tcx> LoopAbstraction<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
    ) {
        self.edge.redirect(from, to);
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for LoopAbstraction<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge
            .label_region_projection(projection, label, repacker)
    }
}
impl<'tcx> MakePlaceOld<'tcx> for LoopAbstraction<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<'tcx> EdgeData<'tcx> for LoopAbstraction<'tcx> {
    fn blocked_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        self.edge.blocked_nodes(repacker)
    }

    fn blocked_by_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.edge.blocked_by_nodes(repacker)
    }
}
impl<'tcx> HasValidityCheck<'tcx> for LoopAbstraction<'tcx> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        self.edge.check_validity(repacker)
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for LoopAbstraction<'tcx> {
    fn to_short_string(&self, _repacker: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "Loop({:?}): {}",
            self.block,
            self.edge.to_short_string(_repacker)
        )
    }
}

impl<'tcx, T> HasPcgElems<T> for LoopAbstraction<'tcx>
where
    AbstractionBlockEdge<'tcx>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut T> {
        self.edge.pcg_elems()
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for LoopAbstraction<'tcx> {
    fn to_borrow_pcg_edge(self, path_conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge::new(
            BorrowPcgEdgeKind::Abstraction(AbstractionType::Loop(self)),
            path_conditions,
        )
    }
}

impl<'tcx> LoopAbstraction<'tcx> {
    pub(crate) fn new(edge: AbstractionBlockEdge<'tcx>, block: BasicBlock) -> Self {
        Self { edge, block }
    }

    pub(crate) fn location(&self) -> Location {
        Location {
            block: self.block,
            statement_index: 0,
        }
    }
}

pub struct AliasNormalizer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub substs: &'tcx [GenericArg<'tcx>],
    pub bindings: FxHashMap<Ty<'tcx>, Ty<'tcx>>,
    pub binders_passed: u32,
}

impl<'tcx> TypeFolder<TyCtxt<'tcx>> for AliasNormalizer<'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_binder<T>(
        &mut self,
        t: infer::canonical::ir::Binder<TyCtxt<'tcx>, T>,
    ) -> infer::canonical::ir::Binder<TyCtxt<'tcx>, T>
    where
        T: TypeFoldable<TyCtxt<'tcx>>,
    {
        self.binders_passed += 1;
        let t = t.super_fold_with(self);
        self.binders_passed -= 1;
        t
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        if !t.has_param() {
            return t;
        }

        match t.kind() {
            // when on a param type, add it to the bindings
            ty::TyKind::Param(param_ty) => {
                let real_ty = self
                    .substs
                    .get(param_ty.index as usize)
                    .unwrap_or_else(|| panic!("parameter {param_ty:#?} out of range"))
                    .expect_ty();
                self.bindings
                    .insert(t, self.shift_vars_through_binders(real_ty));
                t
            }
            // when on an alias, try to resolve it
            // this is the whole point of this folder
            ty::TyKind::Alias(_, alias_ty) => {
                for arg in alias_ty.args {
                    arg.fold_with(self);
                }
                let maybe_normalized = self.normalize_alias(t).fold_with(self);
                self.bindings.insert(t, maybe_normalized);
                maybe_normalized
            }

            // recur on these
            // just args
            ty::TyKind::Adt(adt_def, args) => {
                let args = args.fold_with(self);
                let new_kind = ty::TyKind::Adt(*adt_def, args);
                if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                }
            }
            ty::TyKind::Closure(def_id, args) => {
                let args = args.fold_with(self);
                let new_kind = ty::TyKind::Closure(*def_id, args);
                if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                }
            }
            ty::TyKind::CoroutineClosure(def_id, args) => {
                let args = args.fold_with(self);
                let new_kind = ty::TyKind::CoroutineClosure(*def_id, args);
                if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                }
            }
            ty::TyKind::Coroutine(def_id, args) => {
                let args = args.fold_with(self);
                let new_kind = ty::TyKind::Coroutine(*def_id, args);
                if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                }
            }
            ty::TyKind::CoroutineWitness(def_id, args) => {
                let args = args.fold_with(self);
                let new_kind = ty::TyKind::CoroutineWitness(*def_id, args);
                if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                }
            }
            ty::TyKind::FnDef(def_id, args) => {
                let args = args.fold_with(self);
                let new_kind = ty::TyKind::FnDef(*def_id, args);
                if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                }
            }

            // nested tys
            ty::TyKind::Array(ty, const_) => {
                let ty = ty.fold_with(self);
                let const_ = const_.fold_with(self);
                let new_kind = ty::TyKind::Array(ty, const_);
                let main_ty = if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                };
                if let Some(&subst_ty) = self.bindings.get(&ty) {
                    let real_ty = self
                        .tcx
                        .mk_ty_from_kind(ty::TyKind::Array(subst_ty, const_));
                    self.bindings.insert(main_ty, real_ty);
                }
                main_ty
            }
            ty::TyKind::Pat(ty, pat) => {
                let ty = ty.fold_with(self);
                let pat = pat.fold_with(self);
                let new_kind = ty::TyKind::Pat(ty, pat);
                let main_ty = if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                };
                if let Some(&subst_ty) = self.bindings.get(&ty) {
                    let real_ty = self.tcx.mk_ty_from_kind(ty::TyKind::Pat(subst_ty, pat));
                    self.bindings.insert(main_ty, real_ty);
                }
                main_ty
            }
            ty::TyKind::Slice(ty) => {
                let ty = ty.fold_with(self);
                let new_kind = ty::TyKind::Slice(ty);
                let main_ty = if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                };
                if let Some(&subst_ty) = self.bindings.get(&ty) {
                    let real_ty = self.tcx.mk_ty_from_kind(ty::TyKind::Slice(subst_ty));
                    self.bindings.insert(main_ty, real_ty);
                }
                main_ty
            }
            ty::TyKind::RawPtr(ty, mutbl) => {
                let ty = ty.fold_with(self);
                let new_kind = ty::TyKind::RawPtr(ty, *mutbl);
                let main_ty = if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                };
                if let Some(&subst_ty) = self.bindings.get(&ty) {
                    let real_ty = self
                        .tcx
                        .mk_ty_from_kind(ty::TyKind::RawPtr(subst_ty, *mutbl));
                    self.bindings.insert(main_ty, real_ty);
                }
                main_ty
            }
            ty::TyKind::Ref(region, ty, mutbl) => {
                let region = region.fold_with(self);
                let ty = ty.fold_with(self);
                let new_kind = ty::TyKind::Ref(region, ty, *mutbl);
                let main_ty = if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                };
                if let Some(&subst_ty) = self.bindings.get(&ty) {
                    let real_ty = self
                        .tcx
                        .mk_ty_from_kind(ty::TyKind::Ref(region, subst_ty, *mutbl));
                    self.bindings.insert(main_ty, real_ty);
                }
                main_ty
            }
            ty::TyKind::Tuple(tys) => {
                let tys = tys.fold_with(self);
                let new_kind = ty::TyKind::Tuple(tys);
                if *t.kind() != new_kind {
                    self.tcx.mk_ty_from_kind(new_kind)
                } else {
                    t
                }
            }

            ty::TyKind::FnPtr(..) | ty::TyKind::UnsafeBinder(_) | ty::TyKind::Dynamic(..) => {
                t.super_fold_with(self)
            }

            // keeing these the same
            ty::TyKind::Bool
            | ty::TyKind::Char
            | ty::TyKind::Str
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Float(_)
            | ty::TyKind::Error(_)
            | ty::TyKind::Infer(_)
            | ty::TyKind::Bound(..)
            | ty::TyKind::Placeholder(..)
            | ty::TyKind::Never
            | ty::TyKind::Foreign(..) => return t,
        }
    }
}

impl<'tcx> AliasNormalizer<'tcx> {
    /// Normalizes the given `ty`. This MUST have kind `ty::TyKind::Alias`.
    /// Panics if given a different kind of `Ty`.
    fn normalize_alias(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        let (_alias_ty_kind, alias_ty) =
            if let ty::TyKind::Alias(alias_ty_kind, alias_ty) = ty.kind() {
                (alias_ty_kind, alias_ty)
            } else {
                panic!("`normalize_alias` expected an alias, got {ty:#?}");
            };

        let (trait_ref, _own_args) = alias_ty.trait_ref_and_own_args(self.tcx);
        let mut args = alias_ty.args.iter().collect_vec();

        loop {
            let mut generic_candidates = vec![];
            let mut real_candidates = vec![];

            self.tcx
                .for_each_relevant_impl(trait_ref.def_id, args[0].expect_ty(), |impl_def_id| {
                    println!("{impl_def_id:#?}");
                    if let Some(assoc_def_id) = self
                        .tcx
                        .impl_item_implementor_ids(impl_def_id)
                        .get(&alias_ty.def_id)
                    {
                        let type_of = self.tcx.type_of(*assoc_def_id);
                        let generic_ty = type_of.instantiate_identity();

                        if let Some(bound_ty) = self.bindings.get(&generic_ty) {
                            let real_ty = type_of.instantiate(self.tcx, self.substs);
                            if real_ty == *bound_ty {
                                generic_candidates.push(generic_ty);
                            }
                        } else {
                            real_candidates.push(generic_ty);
                        }
                    }
                });

            if generic_candidates.len() == 1
                && let Some(candidate_ty) = generic_candidates.get(0)
            {
                return *candidate_ty;
            } else if generic_candidates.is_empty()
                && real_candidates.len() == 1
                && let Some(candidate_ty) = real_candidates.get(0)
            {
                return *candidate_ty;
            } else if args.has_param() {
                if let Some(next_arg) = args.iter_mut().skip_while(|arg| !arg.has_param()).next() {
                    *next_arg = (*self.bindings.get(&(*next_arg).expect_ty()).unwrap()).into();
                }
            } else {
                // unable to normalize :(
                break;
            }
        }

        ty
    }

    fn shift_vars_through_binders<T: TypeFoldable<TyCtxt<'tcx>>>(&self, val: T) -> T {
        if self.binders_passed == 0 || !val.has_escaping_bound_vars() {
            val
        } else {
            ty::shift_vars(self.tcx, val, self.binders_passed)
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum FunctionData<'tcx> {
    FnDefData(FnDefData<'tcx>),
    FnPtrData(FnPtrData<'tcx>),
}

impl<'tcx> FunctionData<'tcx> {
    pub fn inputs_and_output(self) -> &'tcx [Ty<'tcx>] {
        match self {
            FunctionData::FnDefData(fn_def_data) => fn_def_data.inputs_and_output(),
            FunctionData::FnPtrData(fn_ptr_data) => fn_ptr_data.inputs_and_output(),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct FnDefData<'tcx> {
    def_id: DefId,
    substs: GenericArgsRef<'tcx>,
    fn_sig: FnSig<'tcx>,
}

impl<'tcx> FnDefData<'tcx> {
    pub fn new(ctxt: CompilerCtxt<'_, 'tcx>, def_id: DefId, substs: GenericArgsRef<'tcx>) -> Self {
        let fn_sig = ctxt
            .tcx()
            .fn_sig(def_id)
            .instantiate_identity()
            .skip_binder();
        Self {
            def_id,
            substs,
            fn_sig,
        }
    }

    pub fn def_id(self) -> DefId {
        self.def_id
    }

    pub fn substs(self) -> GenericArgsRef<'tcx> {
        self.substs
    }

    pub fn fn_sig(self) -> FnSig<'tcx> {
        self.fn_sig
    }

    pub fn inputs_and_output(self) -> &'tcx [Ty<'tcx>] {
        self.fn_sig.inputs_and_output
    }

    /// Normalizes FnDefData, including any aliases.
    pub fn normalize(&mut self, ctxt: CompilerCtxt<'_, 'tcx>) {
        let typing_env = ctxt.body().typing_env(ctxt.tcx());
        let bindings: FxHashMap<Ty<'tcx>, Ty<'tcx>> = FxHashMap::default();

        // the following function erases region information
        // which is a problem further down the road
        match ctxt.tcx().resolve_instance_raw(PseudoCanonicalInput {
            typing_env: typing_env,
            value: (self.def_id, self.substs),
        }) {
            Ok(maybe_instance) if let Some(instance) = maybe_instance => {
                self.def_id = instance.def.def_id();
                self.substs = instance.args;
            }
            _ => (),
        }

        let mut folder = AliasNormalizer {
            tcx: ctxt.tcx(),
            substs: self.substs,
            bindings,
            binders_passed: 0,
        };

        self.fn_sig = ctxt
            .tcx()
            .fn_sig(self.def_id)
            .instantiate_identity()
            .fold_with(&mut folder)
            .skip_binder();
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct FnPtrData<'tcx> {
    fn_sig_tys: FnSigTys<TyCtxt<'tcx>>,
}

impl<'tcx> FnPtrData<'tcx> {
    pub fn new(fn_sig_tys: FnSigTys<TyCtxt<'tcx>>) -> Self {
        Self { fn_sig_tys }
    }

    pub fn fn_sig_tys(self) -> FnSigTys<TyCtxt<'tcx>> {
        self.fn_sig_tys
    }

    pub fn inputs_and_output(self) -> &'tcx [Ty<'tcx>] {
        self.fn_sig_tys.inputs_and_output
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct FunctionCallAbstraction<'tcx> {
    location: Location,
    function_data: FunctionData<'tcx>,
    edge: AbstractionBlockEdge<'tcx>,
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
    ) {
        self.edge.redirect(from, to);
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for FunctionCallAbstraction<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edge
            .label_region_projection(projection, label, repacker)
    }
}

impl<'tcx> MakePlaceOld<'tcx> for FunctionCallAbstraction<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<'tcx> EdgeData<'tcx> for FunctionCallAbstraction<'tcx> {
    fn blocks_node<C: Copy>(
        &self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        self.edge.blocks_node(node, repacker)
    }

    fn blocked_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        self.edge.blocked_nodes(repacker)
    }

    fn blocked_by_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.edge.blocked_by_nodes(repacker)
    }
}

impl<'tcx> HasValidityCheck<'tcx> for FunctionCallAbstraction<'tcx> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        self.edge.check_validity(repacker)
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for FunctionCallAbstraction<'tcx> {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "call{} at {:?}: {}",
            match &self.function_data {
                FunctionData::FnDefData(fn_def_data) =>
                    format!(" {}", ctxt.tcx().def_path_str(fn_def_data.def_id)),
                FunctionData::FnPtrData(_) => "".to_string(),
            },
            self.location,
            self.edge.to_short_string(ctxt)
        )
    }
}

impl<'tcx, T> HasPcgElems<T> for FunctionCallAbstraction<'tcx>
where
    AbstractionBlockEdge<'tcx>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut T> {
        self.edge.pcg_elems()
    }
}

impl<'tcx> FunctionCallAbstraction<'tcx> {
    pub fn def_id(&self) -> Option<DefId> {
        match self.function_data {
            FunctionData::FnDefData(fn_def_data) => Some(fn_def_data.def_id()),
            FunctionData::FnPtrData(_) => None,
        }
    }

    pub fn substs(&self) -> Option<GenericArgsRef<'tcx>> {
        match self.function_data {
            FunctionData::FnDefData(fn_def_data) => Some(fn_def_data.substs()),
            FunctionData::FnPtrData(_) => None,
        }
    }

    pub fn location(&self) -> Location {
        self.location
    }

    pub fn edge(&self) -> &AbstractionBlockEdge<'tcx> {
        &self.edge
    }

    pub fn new(
        location: Location,
        function_data: FunctionData<'tcx>,
        edge: AbstractionBlockEdge<'tcx>,
    ) -> Self {
        Self {
            location,
            function_data,
            edge,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum AbstractionType<'tcx> {
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
}

edgedata_enum!(
    AbstractionType<'tcx>,
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
);

impl<'tcx> AbstractionType<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
    ) {
        match self {
            AbstractionType::FunctionCall(c) => c.redirect(from, to),
            AbstractionType::Loop(c) => c.redirect(from, to),
        }
    }
}

#[derive(Clone, Debug, Hash)]
pub struct AbstractionBlockEdge<'tcx> {
    pub(crate) inputs: SmallVec<[AbstractionInputTarget<'tcx>; 8]>,
    outputs: SmallVec<[MaybeRedirected<AbstractionOutputTarget<'tcx>>; 8]>,
}

impl<'tcx> AbstractionBlockEdge<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
    ) {
        for output in self.outputs.iter_mut() {
            output.redirect(from, to);
        }
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for AbstractionBlockEdge<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for input in self.inputs.iter_mut() {
            changed |= input.label_region_projection(projection, label, repacker);
        }
        for output in self.outputs.iter_mut() {
            changed |= output.label_region_projection(projection, label, repacker);
        }
        changed
    }
}

impl<'tcx> EdgeData<'tcx> for AbstractionBlockEdge<'tcx> {
    fn blocks_node<C: Copy>(
        &self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        match node {
            PCGNode::Place(p) => self.inputs.contains(&p.into()),
            PCGNode::RegionProjection(region_projection) => match region_projection.base {
                MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => self.inputs.contains(
                    &region_projection
                        .with_base(maybe_remote_place, repacker)
                        .into(),
                ),
                MaybeRemoteRegionProjectionBase::Const(_) => false,
            },
        }
    }
    fn blocked_nodes<C: Copy>(
        &self,
        _repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        self.inputs().into_iter().map(|i| i.into()).collect()
    }

    fn blocked_by_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.outputs()
            .into_iter()
            .map(|o| o.to_local_node(repacker))
            .collect()
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for AbstractionBlockEdge<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "[{}] -> [{}]",
            self.inputs
                .iter()
                .map(|i| i.to_short_string(repacker))
                .join(", "),
            self.outputs
                .iter()
                .map(|o| o.to_short_string(repacker))
                .join(", ")
        )
    }
}

impl<'tcx> HasValidityCheck<'tcx> for AbstractionBlockEdge<'tcx> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        for input in self.inputs.iter() {
            input.check_validity(repacker)?;
        }
        for output in self.outputs.iter() {
            output.check_validity(repacker)?;
        }
        Ok(())
    }
}

// impl<'tcx> HasPcgElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for AbstractionBlockEdge<'tcx> {
//     fn pcg_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
//         self.outputs.iter_mut().collect()
//     }
// }

impl PartialEq for AbstractionBlockEdge<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.inputs() == other.inputs() && self.outputs() == other.outputs()
    }
}

impl Eq for AbstractionBlockEdge<'_> {}

impl<'tcx> AbstractionBlockEdge<'tcx> {
    pub(crate) fn new(
        inputs: Vec<AbstractionInputTarget<'tcx>>,
        outputs: Vec<AbstractionOutputTarget<'tcx>>,
    ) -> Self {
        assert!(!inputs.is_empty());
        assert!(!outputs.is_empty());
        Self {
            inputs: inputs.into_iter().collect(),
            outputs: outputs.into_iter().map(|o| o.into()).collect(),
        }
    }

    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.outputs.iter().map(|o| o.effective()).collect()
    }

    pub fn inputs(&self) -> Vec<AbstractionInputTarget<'tcx>> {
        self.inputs.to_vec()
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for AbstractionInputTarget<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            AbstractionInputTarget::Place(p) => p.pcg_elems(),
            AbstractionInputTarget::RegionProjection(rp) => rp.base.pcg_elems(),
        }
    }
}
impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for AbstractionBlockEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut result = vec![];
        for input in self.inputs.iter_mut() {
            result.extend(input.pcg_elems());
        }
        for output in self.outputs.iter_mut() {
            result.extend(output.pcg_elems());
        }
        result
    }
}

impl<'tcx> AbstractionType<'tcx> {
    pub(crate) fn is_function_call(&self) -> bool {
        matches!(self, AbstractionType::FunctionCall(_))
    }

    pub fn location(&self) -> Location {
        match self {
            AbstractionType::FunctionCall(c) => c.location,
            AbstractionType::Loop(c) => c.location(),
        }
    }

    pub fn inputs(&self) -> Vec<AbstractionInputTarget<'tcx>> {
        self.edge().inputs()
    }

    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.edge().outputs()
    }

    pub fn edge(&self) -> &AbstractionBlockEdge<'tcx> {
        match self {
            AbstractionType::FunctionCall(c) => &c.edge,
            AbstractionType::Loop(c) => &c.edge,
        }
    }

    pub fn has_input(&self, node: AbstractionInputTarget<'tcx>) -> bool {
        self.inputs().contains(&node)
    }
}
