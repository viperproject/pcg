// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    borrow::Cow,
    collections::VecDeque,
    fmt::{Debug, Formatter, Result},
};

use rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{
        mir::{
            PlaceElem, PlaceRef, ProjectionElem, RETURN_PLACE, VarDebugInfo, VarDebugInfoContents,
        },
        ty::{AdtKind, TyKind},
    },
    span::Span,
};

use crate::rustc_interface;

use super::{CompilerCtxt, Place};

#[derive(Clone)]
pub enum PlaceDisplay<'tcx> {
    Temporary(Place<'tcx>),
    User(Place<'tcx>, String),
}

impl Debug for PlaceDisplay<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            PlaceDisplay::Temporary(place) => write!(f, "{place:?}"),
            PlaceDisplay::User(place, s) => write!(f, "{place:?} = {s}"),
        }
    }
}

impl PlaceDisplay<'_> {
    pub fn is_user(&self) -> bool {
        matches!(self, PlaceDisplay::User(..))
    }
}

pub trait DisplayWithCompilerCtxt<'tcx, BC: Copy> {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String;
}

impl<'tcx, T: DisplayWithCompilerCtxt<'tcx, BC>, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC>
    for Vec<T>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        let comma_sep = self
            .iter()
            .map(|t| t.to_short_string(ctxt))
            .collect::<Vec<_>>()
            .join(", ");
        format!("[{comma_sep}]")
    }
}

impl<'tcx, T: DisplayWithCompilerCtxt<'tcx, BC>, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC>
    for FxHashSet<T>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        let comma_sep = self
            .iter()
            .map(|t| t.to_short_string(ctxt))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{{{comma_sep}}}")
    }
}

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for Place<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> String {
        match self.to_string(repacker) {
            PlaceDisplay::Temporary(p) => format!("{p:?}"),
            PlaceDisplay::User(_p, s) => s,
        }
    }
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn to_json<BC: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        serde_json::Value::String(self.to_short_string(ctxt))
    }

    pub fn to_string<BC: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> PlaceDisplay<'tcx> {
        // Get the local's debug name from the Body's VarDebugInfo
        let local_name = if self.local == RETURN_PLACE {
            Cow::Borrowed("RETURN")
        } else {
            fn as_local(span: Span, outer_span: Span) -> Option<Span> {
                // Before we call source_callsite, we check and see if the span is already local.
                // This is important b/c in print!("{}", y) if the user selects `y`, the source_callsite
                // of that span is the entire macro.
                if outer_span.contains(span) {
                    return Some(span);
                } else {
                    let sp = span.source_callsite();
                    if outer_span.contains(sp) {
                        return Some(sp);
                    }
                }

                None
            }

            let get_local_name = |info: &VarDebugInfo<'tcx>| match info.value {
                VarDebugInfoContents::Place(place) if place.local == self.local => {
                    as_local(info.source_info.span, repacker.mir.span)
                        .map(|_| info.name.to_string())
                }
                _ => None,
            };
            let Some(local_name) = repacker.mir.var_debug_info.iter().find_map(get_local_name)
            else {
                return PlaceDisplay::Temporary(*self);
            };
            Cow::Owned(local_name)
        };

        #[derive(Copy, Clone)]
        enum ElemPosition {
            Prefix,
            Suffix,
        }

        // Turn each PlaceElem into a prefix (e.g. * for deref) or a suffix
        // (e.g. .field for projection).
        let elem_to_string = |(index, (place, elem)): (
            usize,
            (PlaceRef<'tcx>, PlaceElem<'tcx>),
        )|
         -> (ElemPosition, Cow<'static, str>) {
            match elem {
                ProjectionElem::Deref => (ElemPosition::Prefix, "*".into()),

                ProjectionElem::Field(field, _) => {
                    let ty = place.ty(&repacker.mir.local_decls, repacker.tcx()).ty;

                    let field_name = match ty.kind() {
                        TyKind::Adt(def, _substs) => {
                            let fields = match def.adt_kind() {
                                AdtKind::Struct | AdtKind::Union => &def.non_enum_variant().fields,
                                AdtKind::Enum => {
                                    let Some(PlaceElem::Downcast(_, variant_idx)) =
                                        self.projection.get(index - 1)
                                    else {
                                        unimplemented!()
                                    };
                                    &def.variant(*variant_idx).fields
                                }
                            };

                            fields[field].ident(repacker.tcx()).to_string()
                        }

                        TyKind::Tuple(_) => field.as_usize().to_string(),

                        TyKind::Closure(def_id, _substs) => match def_id.as_local() {
                            Some(local_def_id) => {
                                let captures = repacker.tcx().closure_captures(local_def_id);
                                captures[field.as_usize()].var_ident.to_string()
                            }
                            None => field.as_usize().to_string(),
                        },

                        kind => unimplemented!("{kind:?}"),
                    };

                    (ElemPosition::Suffix, format!(".{field_name}").into())
                }
                ProjectionElem::Downcast(sym, _) => {
                    let variant = sym.map(|s| s.to_string()).unwrap_or_else(|| "??".into());
                    (ElemPosition::Suffix, format!("@{variant}",).into())
                }

                ProjectionElem::Index(idx) => (ElemPosition::Suffix, format!("[{idx:?}]").into()),
                ProjectionElem::ConstantIndex { .. } => {
                    (ElemPosition::Suffix, format!("[{elem:?}]").into())
                }
                ProjectionElem::Subslice { .. } => {
                    (ElemPosition::Suffix, format!("[{elem:?}]").into())
                }
                kind => unimplemented!("{kind:?}"),
            }
        };

        let (positions, contents): (Vec<_>, Vec<_>) = self
            .iter_projections()
            .enumerate()
            .map(elem_to_string)
            .unzip();

        // Combine the prefixes and suffixes into a corresponding sequence
        let mut parts = VecDeque::from([local_name]);
        for (i, string) in contents.into_iter().enumerate() {
            match positions[i] {
                ElemPosition::Prefix => {
                    parts.push_front(string);
                    if matches!(positions.get(i + 1), Some(ElemPosition::Suffix)) {
                        parts.push_front(Cow::Borrowed("("));
                        parts.push_back(Cow::Borrowed(")"));
                    }
                }
                ElemPosition::Suffix => parts.push_back(string),
            }
        }

        let full = parts.make_contiguous().join("");
        PlaceDisplay::User(*self, full)
    }
}

pub(crate) trait DebugLines<Ctxt> {
    fn debug_lines(&self, ctxt: Ctxt) -> Vec<String>;
}
