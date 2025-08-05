use crate::{
    pcg_validity_assert, pcg_validity_expect_ok, validity_checks_enabled, validity_checks_warn_only,
};

use super::CompilerCtxt;

pub trait HasValidityCheck<'tcx> {
    fn check_validity(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Result<(), String>;

    fn assert_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) {
        pcg_validity_expect_ok!(self.check_validity(ctxt), fallback: (), [ctxt], "Validity check failed");
    }

    fn is_valid(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.check_validity(ctxt).is_ok()
    }
}
