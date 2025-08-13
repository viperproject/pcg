use crate::rustc_interface::middle::mir;
use crate::utils::HasBorrowCheckerCtxt;
use crate::{pcg_validity_assert, pcg_validity_expect_ok};

use super::CompilerCtxt;

pub trait HasValidityCheck<'tcx> {
    fn check_validity(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Result<(), String>;

    fn assert_validity<'a>(&self, ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>)
    where
        'tcx: 'a,
    {
        pcg_validity_expect_ok!(self.check_validity(ctxt.bc_ctxt()), fallback: (), [ctxt], "Validity check failed");
    }

    fn assert_validity_at_location(&self, location: mir::Location, ctxt: CompilerCtxt<'_, 'tcx>) {
        pcg_validity_expect_ok!(self.check_validity(ctxt), fallback: (), [ctxt at location]);
    }

    fn is_valid<'a>(&self, ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        self.check_validity(ctxt.bc_ctxt()).is_ok()
    }
}
