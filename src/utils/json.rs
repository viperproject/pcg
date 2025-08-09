use crate::utils::CompilerCtxt;

pub trait ToJsonWithCompilerCtxt<'tcx, BC> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value;
}

impl<'tcx, BC: Copy, T: ToJsonWithCompilerCtxt<'tcx, BC>> ToJsonWithCompilerCtxt<'tcx, BC>
    for Vec<T>
{
    fn to_json(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        self.iter()
            .map(|a| a.to_json(ctxt))
            .collect::<Vec<_>>()
            .into()
    }
}
