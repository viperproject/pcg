use super::PlaceRepacker;

pub trait HasValidityCheck<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String>;

    fn assert_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) {
        if let Err(e) = self.check_validity(repacker) {
            panic!("{}", e);
        }
    }

    fn is_valid(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.check_validity(repacker).is_ok()
    }
}
