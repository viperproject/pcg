use std::fmt::Display;

use crate::free_pcs::CapabilityKind;

use super::has_pcs_elem::HasPcsElems;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct WithCapability<T> {
    value: T,
    capability: Option<CapabilityKind>,
}

impl<'tcx, U, T: HasPcsElems<U>> HasPcsElems<U> for WithCapability<T> {
    fn pcs_elems(&mut self) -> Vec<&mut U> {
        self.value.pcs_elems()
    }
}

impl<'tcx, T: Display> Display for WithCapability<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)?;
        if let Some(capability) = self.capability {
            write!(f, ": {:?}", capability)?;
        } else {
            write!(f, ": ∅")?;
        }
        Ok(())
    }
}

impl<'tcx, T> WithCapability<T> {
    pub fn new(value: T, capability: Option<CapabilityKind>) -> Self {
        Self { value, capability }
    }
}
