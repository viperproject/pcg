use crate::rustc_interface::{
    index::IndexVec,
    middle::ty::{self, TypeSuperVisitable, TypeVisitable, TypeVisitor},
};

use super::region_projection::{FromRegion, RegionIdx};
use crate::utils::CompilerCtxt;

pub(crate) struct LifetimeExtractor<'tcx> {
    pub(crate) lifetimes: Vec<ty::Region<'tcx>>,
    #[allow(dead_code)]
    pub(crate) tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for LifetimeExtractor<'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.kind() {
            ty::TyKind::Closure(_, args) => {
                let closure_args = args.as_closure();
                let upvar_tys = closure_args.upvar_tys();
                for ty in upvar_tys.iter() {
                    self.visit_ty(ty);
                }
            }
            _ => {
                ty.super_visit_with(self);
            }
        }
    }
    fn visit_region(&mut self, rr: ty::Region<'tcx>) {
        if !self.lifetimes.contains(&rr) {
            self.lifetimes.push(rr);
        }
    }
}

/// Returns all of the (possibly nested) regions in `ty` that could be part of
/// its region projection. In particular, the intention of this function is to
/// *only* return regions that correspond to data borrowed in a type. In
/// particular, for closures / functions, we do not include regions in the input
/// or argument types.
/// If this type is a reference type, e.g. `&'a mut T`, then this will return
/// `'a` and the regions within `T`.
///
/// The resulting list does not contain duplicates, e.g. T<'a, 'a> will return
/// `['a]`. Note that the order of the returned regions is arbitrary, but
/// consistent between calls to types with the same "shape". E.g T<'a, 'b> and
/// T<'c, 'd> will return the same list of regions will return `['a, 'b]` and
/// `['c, 'd]` respectively. This enables substitution of regions to handle
/// moves in the PCG e.g for the statement `let x: T<'a, 'b> = move c: T<'c,
/// 'd>`.
pub(crate) fn extract_regions<'tcx, C: Copy, R: FromRegion<'tcx>>(
    ty: ty::Ty<'tcx>,
    repacker: CompilerCtxt<'_, 'tcx, C>,
) -> IndexVec<RegionIdx, R> {
    let mut visitor = LifetimeExtractor {
        lifetimes: vec![],
        tcx: repacker.tcx(),
    };
    ty.visit_with(&mut visitor);
    IndexVec::from_iter(visitor.lifetimes.iter().map(|r| (*r).into()))
}

#[allow(unused)]
pub(crate) fn extract_inner_regions<'tcx, R: FromRegion<'tcx>>(
    ty: ty::Ty<'tcx>,
    repacker: CompilerCtxt<'_, 'tcx>,
) -> IndexVec<RegionIdx, R> {
    if let ty::TyKind::Ref(_, ty, _) = ty.kind() {
        extract_regions(*ty, repacker)
    } else {
        extract_regions(ty, repacker)
    }
}
