use crate::borrow_pcg::{
    edge_data::LabelPlacePredicate,
    has_pcs_elem::{
        HasPcgElems, LabelPlace, LabelRegionProjection, LabelRegionProjectionPredicate,
    },
    latest::Latest,
    region_projection::{RegionProjection, RegionProjectionLabel},
};

use super::{
    display::DisplayWithCompilerCtxt, maybe_old::MaybeOldPlace, validity::HasValidityCheck,
    CompilerCtxt,
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct MaybeRedirected<T, U = T> {
    original: T,
    redirected: Option<U>,
}

impl<'tcx, T: LabelPlace<'tcx>> LabelPlace<'tcx> for MaybeRedirected<T> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = self.original.label_place(predicate, latest, ctxt);
        if let Some(r) = &mut self.redirected {
            changed |= r.label_place(predicate, latest, ctxt);
        }
        changed
    }
}

impl<T> From<T> for MaybeRedirected<T> {
    fn from(original: T) -> Self {
        Self {
            original,
            redirected: None,
        }
    }
}

impl<T: Copy> MaybeRedirected<T> {
    pub(crate) fn effective(&self) -> T {
        self.redirected.unwrap_or(self.original)
    }
}

impl<T: Copy + Eq> MaybeRedirected<T> {
    pub(crate) fn redirect(&mut self, from: T, to: T) {
        if self.effective() == from {
            self.redirected = Some(to);
        }
    }

    fn collapse_if_equal(&mut self) {
        if let Some(o2) = &self.redirected
            && self.original == *o2
        {
            self.redirected = None
        }
    }
}

impl<'tcx, T: Copy + Eq + LabelRegionProjection<'tcx>> LabelRegionProjection<'tcx>
    for MaybeRedirected<T>
{
    fn label_region_projection(
        &mut self,
        predicate: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = self
            .original
            .label_region_projection(predicate, label, repacker);
        if let Some(r) = &mut self.redirected {
            changed |= r.label_region_projection(predicate, label, repacker);
        }
        self.collapse_if_equal();
        changed
    }
}

impl<E, T: HasPcgElems<E>> HasPcgElems<E> for MaybeRedirected<T> {
    fn pcg_elems(&mut self) -> Vec<&mut E> {
        let mut elems = self.original.pcg_elems();
        if let Some(r) = &mut self.redirected {
            elems.extend(r.pcg_elems());
        }
        elems
    }
}

impl<'tcx, BC: Copy, T: DisplayWithCompilerCtxt<'tcx, BC>> DisplayWithCompilerCtxt<'tcx, BC>
    for MaybeRedirected<T>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        if let Some(r) = &self.redirected {
            r.to_short_string(ctxt).to_string()
        } else {
            self.original.to_short_string(ctxt).to_string()
        }
    }
}

impl<'tcx, T: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for MaybeRedirected<T> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.original.check_validity(ctxt)?;
        if let Some(r) = &self.redirected {
            r.check_validity(ctxt)?;
        }
        Ok(())
    }
}
