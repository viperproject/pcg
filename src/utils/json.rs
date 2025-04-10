use crate::utils::CompilerCtxt;

pub trait ToJsonWithCompilerCtxt<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx,'_>) -> serde_json::Value;
}

impl<'tcx, T: ToJsonWithCompilerCtxt<'tcx>> ToJsonWithCompilerCtxt<'tcx> for Vec<T> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx,'_>) -> serde_json::Value {
        self.iter()
            .map(|a| a.to_json(repacker))
            .collect::<Vec<_>>()
            .into()
    }
}
