// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_interface::middle::{
    mir::{
        visit::Visitor, Local, Location, Operand, ProjectionElem, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind, RETURN_PLACE,
    },
    ty,
};

use crate::{
    free_pcs::CapabilityKind,
    rustc_interface,
    utils::{Place, PlaceRepacker},
};

use super::CapabilitySummary;

pub(crate) struct Triple<'tcx> {
    pre: Condition<'tcx>,
    post: Condition<'tcx>,
}

impl<'tcx> Triple<'tcx> {
    pub fn pre(&self) -> &Condition<'tcx> {
        &self.pre
    }
    pub fn post(&self) -> &Condition<'tcx> {
        &self.post
    }
}

#[derive(Clone)]
pub(crate) enum Condition<'tcx> {
    Capability(Place<'tcx>, CapabilityKind),
    AllocateOrDeallocate(Local),
    Unalloc(Local),
    Unchanged,
}

impl<'tcx> Condition<'tcx> {
    fn capability(place: Place<'tcx>, kind: CapabilityKind) -> Condition<'tcx> {
        Condition::Capability(place, kind)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    Before,
    Main,
}

pub(crate) struct TripleWalker<'a, 'b, 'tcx> {
    pub(crate) summary: &'a mut CapabilitySummary<'tcx>,
    repacker: PlaceRepacker<'b, 'tcx>,
    stage: Stage,
    preparing: bool,
}

impl<'a, 'b, 'tcx> TripleWalker<'a, 'b, 'tcx> {
    pub(crate) fn prepare(
        summary: &'a mut CapabilitySummary<'tcx>,
        repacker: PlaceRepacker<'b, 'tcx>,
        stage: Stage,
    ) -> Self {
        Self {
            summary,
            repacker,
            stage,
            preparing: true,
        }
    }
    pub(crate) fn apply(
        summary: &'a mut CapabilitySummary<'tcx>,
        repacker: PlaceRepacker<'b, 'tcx>,
        stage: Stage,
    ) -> Self {
        Self {
            summary,
            repacker,
            stage,
            preparing: false,
        }
    }
    fn triple(&mut self, stage: Stage, t: Triple<'tcx>) {
        if stage != self.stage {
            return;
        }
        if self.preparing {
            self.summary.requires(t.pre, self.repacker);
        } else {
            self.summary.ensures(t, self.repacker);
        }
    }
}

fn get_place_to_expand_to<'b, 'tcx>(
    place: Place<'tcx>,
    repacker: PlaceRepacker<'b, 'tcx>,
) -> Place<'tcx> {
    let mut curr_place: Place<'tcx> = place.local.into();
    for elem in place.projection {
        if *elem == ProjectionElem::Deref && curr_place.ty(repacker).ty.is_ref() {
            return curr_place;
        }

        let place_ty = curr_place.ty(repacker);

        // For some reason the field projection may yield a different lifetime parameter
        // what is expected based on the ADT definition and substs.
        // We use the ADT definition because it will ensure that in the PCS the lifetime parameter
        // of all fields relates to the parameter of their parent struct.
        if let (ProjectionElem::Field(field_idx, _), ty::TyKind::Adt(def, substs)) =
            (elem, place_ty.ty.kind())
        {
            let variant = match place_ty.variant_index {
                Some(v) => def.variant(v),
                None => def.non_enum_variant(),
            };
            let expected_ty = variant.fields[*field_idx].ty(repacker.tcx(), substs);
            curr_place =
                curr_place.mk_place_elem(ProjectionElem::Field(*field_idx, expected_ty), repacker);
        } else {
            curr_place = curr_place.mk_place_elem(*elem, repacker);
        }
    }
    return curr_place;
}

impl<'tcx> Visitor<'tcx> for TripleWalker<'_, '_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        let t = match *operand {
            Operand::Copy(place) => {
                let place: Place<'tcx> = place.into();
                let place_to_expand_to = get_place_to_expand_to(place, self.repacker);
                let pre = Condition::Capability(place_to_expand_to, CapabilityKind::Exclusive);
                Triple {
                    pre,
                    post: Condition::Unchanged,
                }
            }
            Operand::Move(place) => Triple {
                pre: Condition::Capability(place.into(), CapabilityKind::Exclusive),
                post: Condition::Capability(place.into(), CapabilityKind::Write),
            },
            Operand::Constant(..) => return,
        };
        self.triple(Stage::Before, t)
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        self.super_rvalue(rvalue, location);
        use Rvalue::*;
        match rvalue {
            Use(_)
            | Repeat(_, _)
            | ThreadLocalRef(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Aggregate(_, _)
            | ShallowInitBox(_, _) => {}

            &Ref(_, _, place) | &Len(place) | &Discriminant(place) | &CopyForDeref(place) => {
                let place: Place<'tcx> = place.into();
                let place_to_expand_to = get_place_to_expand_to(place, self.repacker);
                eprintln!(
                    "expand for rvalue {:?}: {:?} to {:?}: {:?}",
                    rvalue,
                    rvalue.ty(self.repacker.body(), self.repacker.tcx()),
                    place_to_expand_to,
                    place_to_expand_to.ty(self.repacker)
                );
                self.triple(
                    Stage::Before,
                    Triple {
                        pre: Condition::Capability(place_to_expand_to, CapabilityKind::Exclusive),
                        post: Condition::Unchanged,
                    },
                )
            }
            _ => todo!(),
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);
        use StatementKind::*;
        let t = match &statement.kind {
            &Assign(box (place, _)) => {
                let place: Place<'_> = place.into();
                let place_to_expand_to = get_place_to_expand_to(place, self.repacker);
                let cond = Condition::Capability(place_to_expand_to, CapabilityKind::Exclusive);
                Triple {
                    pre: cond.clone(),
                    post: cond,
                }
            }
            &FakeRead(box (_, place)) => Triple {
                pre: Condition::capability(
                    get_place_to_expand_to(place.into(), self.repacker),
                    CapabilityKind::Exclusive,
                ),
                post: Condition::Unchanged,
            },
            &PlaceMention(box place) => Triple {
                pre: Condition::capability(
                    get_place_to_expand_to(place.into(), self.repacker),
                    CapabilityKind::Write,
                ),
                post: Condition::Unchanged,
            },
            &SetDiscriminant { box place, .. } => Triple {
                pre: Condition::capability(
                    get_place_to_expand_to(place.into(), self.repacker),
                    CapabilityKind::Exclusive,
                ),
                post: Condition::Unchanged,
            },
            &Deinit(box place) => Triple {
                pre: Condition::capability(
                    get_place_to_expand_to(place.into(), self.repacker),
                    CapabilityKind::Exclusive,
                ),
                post: Condition::capability(
                    get_place_to_expand_to(place.into(), self.repacker),
                    CapabilityKind::Write,
                ),
            },
            &StorageLive(local) => Triple {
                pre: Condition::Unalloc(local),
                post: Condition::AllocateOrDeallocate(local),
            },
            &StorageDead(local) => Triple {
                pre: Condition::AllocateOrDeallocate(local),
                post: Condition::Unalloc(local),
            },
            &Retag(_, box place) => Triple {
                pre: Condition::capability(
                    get_place_to_expand_to(place.into(), self.repacker),
                    CapabilityKind::Exclusive,
                ),
                post: Condition::Unchanged,
            },
            AscribeUserType(..) | Coverage(..) | Intrinsic(..) | ConstEvalCounter | Nop => return,
        };
        self.triple(Stage::Main, t);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location);
        use TerminatorKind::*;
        let t = match &terminator.kind {
            Goto { .. }
            | SwitchInt { .. }
            | UnwindResume
            | UnwindTerminate(_)
            | Unreachable
            | Assert { .. }
            | FalseEdge { .. }
            | FalseUnwind { .. } => return,
            Return => {
                let always_live = self.repacker.always_live_locals();
                for local in 0..self.repacker.local_count() {
                    let local = Local::from_usize(local);
                    let pre = if local == RETURN_PLACE {
                        Condition::Capability(RETURN_PLACE.into(), CapabilityKind::Exclusive)
                    } else if always_live.contains(local) {
                        Condition::Capability(local.into(), CapabilityKind::Write)
                    } else {
                        Condition::Unalloc(local)
                    };
                    self.triple(
                        Stage::Main,
                        Triple {
                            pre,
                            post: Condition::Unchanged,
                        },
                    );
                }
                return;
            }
            &Drop { place, .. } => Triple {
                pre: Condition::Capability(
                    get_place_to_expand_to(place.into(), self.repacker),
                    CapabilityKind::Write,
                ),
                post: Condition::Capability(
                    get_place_to_expand_to(place.into(), self.repacker),
                    CapabilityKind::Write,
                ),
            },
            &Call { destination, .. } => Triple {
                pre: Condition::Capability(
                    get_place_to_expand_to(destination.into(), self.repacker),
                    CapabilityKind::Write,
                ),
                post: Condition::Capability(
                    get_place_to_expand_to(destination.into(), self.repacker),
                    CapabilityKind::Exclusive,
                ),
            },
            &Yield { resume_arg, .. } => Triple {
                pre: Condition::Capability(resume_arg.into(), CapabilityKind::Write),
                post: Condition::Capability(resume_arg.into(), CapabilityKind::Exclusive),
            },
            InlineAsm { .. } => todo!("{terminator:?}"),
            CoroutineDrop => todo!(),
            _ => todo!("{terminator:?}"),
        };
        self.triple(Stage::Main, t);
    }
}
