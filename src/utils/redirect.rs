use crate::borrow_pcg::{
    has_pcs_elem::{HasPcgElems, LabelRegionProjection},
    region_projection::RegionProjection,
};

use super::{
    display::DisplayWithCompilerCtxt, maybe_old::MaybeOldPlace, validity::HasValidityCheck,
    CompilerCtxt, SnapshotLocation,
};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct MaybeRedirected<T, U = T> {
    original: T,
    redirected: Option<U>,
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
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        location: SnapshotLocation,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = self
            .original
            .label_region_projection(projection, location, repacker);
        if let Some(r) = &mut self.redirected {
            changed |= r.label_region_projection(projection, location, repacker);
        }
        self.collapse_if_equal();
        changed
    }
}

impl<'tcx, E, T: HasPcgElems<E>> HasPcgElems<E> for MaybeRedirected<T> {
    fn pcg_elems(&mut self) -> Vec<&mut E> {
        let mut elems = self.original.pcg_elems();
        if let Some(r) = &mut self.redirected {
            elems.extend(r.pcg_elems());
        }
        elems
    }
}

impl<'tcx, T: DisplayWithCompilerCtxt<'tcx>> DisplayWithCompilerCtxt<'tcx> for MaybeRedirected<T> {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        if let Some(r) = &self.redirected {
            format!("{}", r.to_short_string(ctxt))
        } else {
            format!("{}", self.original.to_short_string(ctxt))
        }
    }
}

impl<'tcx, T: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for MaybeRedirected<T> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        self.original.check_validity(repacker)?;
        if let Some(r) = &self.redirected {
            r.check_validity(repacker)?;
        }
        Ok(())
    }
}
