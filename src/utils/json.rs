use crate::utils::PlaceRepacker;

pub trait ToJsonWithRepacker<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value;
}

impl<'tcx, T: ToJsonWithRepacker<'tcx>> ToJsonWithRepacker<'tcx> for Vec<T> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        self.iter()
            .map(|a| a.to_json(repacker))
            .collect::<Vec<_>>()
            .into()
    }
}