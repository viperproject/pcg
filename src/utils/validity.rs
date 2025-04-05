use crate::validity_checks_enabled;

use super::CompilerCtxt;

pub trait HasValidityCheck<'tcx> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String>;

    fn assert_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) {
        if validity_checks_enabled()
            && let Err(e) = self.check_validity(repacker)
        {
            panic!("{}", e);
        }
    }

    fn is_valid(&self, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.check_validity(repacker).is_ok()
    }
}
