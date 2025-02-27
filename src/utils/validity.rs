use super::{env_feature_enabled, PlaceRepacker};

pub trait HasValidityCheck<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String>;

    fn assert_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) {
        if validity_checks_enabled()
            && let Err(e) = self.check_validity(repacker)
        {
            panic!("{}", e);
        }
    }

    fn is_valid(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.check_validity(repacker).is_ok()
    }
}

pub(crate) fn validity_checks_enabled() -> bool {
    env_feature_enabled("PCG_VALIDITY_CHECKS").unwrap_or(cfg!(debug_assertions))
}
