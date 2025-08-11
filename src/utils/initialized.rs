use std::{cell::RefCell, rc::Rc};

use crate::{
    compute_fixpoint,
    rustc_interface::{
        middle::{mir, ty},
        mir_dataflow::{
            ResultsCursor,
            impls::MaybeUninitializedPlaces,
            move_paths::{LookupResult, MoveData},
        },
    },
    utils::Place,
};

#[derive(Clone)]
pub(crate) struct DefinitelyInitialized<'a, 'tcx> {
    cursor: Rc<RefCell<ResultsCursor<'a, 'tcx, MaybeUninitializedPlaces<'a, 'tcx>>>>,
    move_data: &'a MoveData<'tcx>,
}

impl<'a, 'tcx> DefinitelyInitialized<'a, 'tcx> {
    pub(crate) fn new(
        tcx: ty::TyCtxt<'tcx>,
        body: &'a mir::Body<'tcx>,
        move_data: &'a MoveData<'tcx>,
    ) -> Self {
        Self {
            cursor: Rc::new(RefCell::new(
                compute_fixpoint(
                    MaybeUninitializedPlaces::new(tcx, body, move_data),
                    tcx,
                    body,
                )
                .into_results_cursor(body),
            )),
            move_data,
        }
    }

    pub(crate) fn is_definitely_initialized(
        &self,
        location: mir::Location,
        place: Place<'tcx>,
    ) -> bool {
        let idx = match self.move_data.rev_lookup.find(place.into()) {
            LookupResult::Exact(move_path_index) => move_path_index,
            LookupResult::Parent(Some(move_path_index)) => move_path_index,
            LookupResult::Parent(None) => return false,
        };
        let mut cursor = self.cursor.borrow_mut();
        cursor.seek_after_primary_effect(location);
        // If the place is not maybe uninitialized, it is definitely initialized.
        !cursor.get().contains(idx)
    }
}
