use crate::validity_checks_enabled;

use super::CompilerCtxt;

pub trait HasValidityCheck<'tcx> {
    fn check_validity(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Result<(), String>;

    fn assert_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) {
        if validity_checks_enabled()
            && let Err(e) = self.check_validity(ctxt)
        {
            panic!("{}", e);
        }
    }

    fn is_valid(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.check_validity(ctxt).is_ok()
    }
}

#[macro_export]
macro_rules! derive_has_validity_check {
    // For structs with named fields
    (struct $name:ident $(<$($generic:ident),*>)? {
        $($field_name:ident: $field_type:ty),* $(,)?
    }) => {
        impl<'tcx $(, $($generic),*)?> $crate::utils::validity::HasValidityCheck<'tcx> for $name $(<$($generic),*>)?
        where
            $($field_type: $crate::utils::validity::HasValidityCheck<'tcx>,)*
            $($($generic: $crate::utils::validity::HasValidityCheck<'tcx>,)*)?
        {
            fn check_validity(&self, ctxt: $crate::utils::CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
                $(
                    self.$field_name.check_validity(ctxt)?;
                )*
                Ok(())
            }
        }
    };

    // For enums with data variants
    (enum $name:ident $(<$($generic:ident),*>)? {
        $($variant:ident($variant_type:ty)),* $(,)?
    }) => {
        impl<'tcx $(, $($generic),*)?> $crate::utils::validity::HasValidityCheck<'tcx> for $name $(<$($generic),*>)?
        where
            $($variant_type: $crate::utils::validity::HasValidityCheck<'tcx>,)*
            $($($generic: $crate::utils::validity::HasValidityCheck<'tcx>,)*)?
        {
            fn check_validity(&self, ctxt: $crate::utils::CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
                match self {
                    $(
                        $name::$variant(inner) => inner.check_validity(ctxt),
                    )*
                }
            }
        }
    };

    // For enums with unit variants
    (enum $name:ident $(<$($generic:ident),*>)? {
        $($variant:ident),* $(,)?
    }) => {
        impl<'tcx $(, $($generic),*)?> $crate::utils::validity::HasValidityCheck<'tcx> for $name $(<$($generic),*>)? {
            fn check_validity(&self, _ctxt: $crate::utils::CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
                Ok(())
            }
        }
    };

        // For enums with mixed variants (unit and data) - more complex case
    (enum $name:ident $(<$($generic:ident),*>)? {
        $($variant:ident $({ $($field:ident: $field_type:ty),* $(,)? })? $(($inner_type:ty))?),* $(,)?
    }) => {
        impl<'tcx $(, $($generic),*)?> $crate::utils::validity::HasValidityCheck<'tcx> for $name $(<$($generic),*>)?
        where
            $($($($field_type: $crate::utils::validity::HasValidityCheck<'tcx>,)*)*)*
            $($($inner_type: $crate::utils::validity::HasValidityCheck<'tcx>,)*)*
            $($($generic: $crate::utils::validity::HasValidityCheck<'tcx>,)*)?
        {
            fn check_validity(&self, ctxt: $crate::utils::CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
                match self {
                    $(
                        $name::$variant $({ $($field,)* })? $(inner)? => {
                            $($($field.check_validity(ctxt)?;)*)*
                            $(inner.check_validity(ctxt)?)*
                            Ok(())
                        }
                    ),*
                }
            }
        }
    };
}

/// A convenience macro that allows derive-like syntax for HasValidityCheck
/// Usage: has_validity_check!(struct MyStruct<T> { field1: T, field2: SomeType })
///        has_validity_check!(enum MyEnum { Variant1(Type1), Variant2(Type2) })
#[macro_export]
macro_rules! has_validity_check {
    ($($tokens:tt)*) => {
        $crate::derive_has_validity_check!($($tokens)*);
    };
}

pub use derive_has_validity_check;
pub use has_validity_check;
