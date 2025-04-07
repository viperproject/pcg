use crate::validity_checks_enabled;

use super::CompilerCtxt;

pub trait HasValidityCheck<'tcx> {
    fn check_validity<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, '_, C>,
    ) -> Result<(), String>;

    fn assert_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, '_, C>) {
        if validity_checks_enabled()
            && let Err(e) = self.check_validity(repacker)
        {
            panic!("{}", e);
        }
    }

    fn is_valid<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, '_, C>) -> bool {
        self.check_validity(repacker).is_ok()
    }
}
