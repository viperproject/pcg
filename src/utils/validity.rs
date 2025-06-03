use crate::{validity_checks_enabled, validity_checks_warn_only};

use super::CompilerCtxt;

pub trait HasValidityCheck<'tcx> {
    fn check_validity(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Result<(), String>;

    fn assert_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) {
        if validity_checks_enabled()
            && let Err(e) = self.check_validity(ctxt)
        {
            if validity_checks_warn_only() {
                tracing::error!("Validity check failed: {}", e);
            } else {
                panic!("{}", e);
            }
        }
    }

    fn is_valid(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.check_validity(ctxt).is_ok()
    }
}
