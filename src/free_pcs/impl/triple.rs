// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{
    self, BorrowKind, Local, Location, MutBorrowKind, Operand, ProjectionElem,
    Rvalue, Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
};

use crate::utils::visitor::FallableVisitor;
use crate::{
    pcg::{PCGUnsupportedError, PcgError},
    free_pcs::CapabilityKind,
    utils::{display::DisplayWithRepacker, Place, PlaceRepacker},
};

#[derive(Debug, Clone, Copy)]
pub(crate) struct Triple<'tcx> {
    pre: Condition<'tcx>,
    post: Option<Condition<'tcx>>,
}

impl<'tcx> Triple<'tcx> {
    pub fn pre(self) -> Condition<'tcx> {
        self.pre
    }
    pub fn post(self) -> Option<Condition<'tcx>> {
        self.post
    }

    /// Replace all places in the `Condition` with ones that are just above the
    /// first dereference of a ref.
    pub fn replace_place<'b>(self, repacker: PlaceRepacker<'b, 'tcx>) -> Self {
        Self {
            pre: self.pre.fpcg_condition(repacker),
            post: self.post.map(|c| c.fpcg_condition(repacker)),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Condition<'tcx> {
    Capability(Place<'tcx>, CapabilityKind),
    RemoveCapability(Place<'tcx>),
    AllocateOrDeallocate(Local),
    Unalloc(Local),
    Return,
}

impl<'tcx> Condition<'tcx> {
    fn new<T: Into<Place<'tcx>>>(place: T, capability: CapabilityKind) -> Condition<'tcx> {
        Condition::Capability(place.into(), capability)
    }

    fn exclusive<T: Into<Place<'tcx>>>(
        place: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Condition<'tcx> {
        let place = place.into();
        pcg_validity_assert!(
            !place.projects_shared_ref(repacker),
            "Cannot get exclusive on projection of shared ref {}",
            place.to_short_string(repacker)
        );
        Self::new(place, CapabilityKind::Exclusive)
    }

    fn write<T: Into<Place<'tcx>>>(place: T) -> Condition<'tcx> {
        Self::new(place, CapabilityKind::Write)
    }

    fn read<T: Into<Place<'tcx>>>(place: T) -> Condition<'tcx> {
        Self::new(place, CapabilityKind::Read)
    }

    /// Returns the condition for the place in the free PCG. If the place is
    /// already in the free PCG, this will be the same condition. However, if
    /// the place is in the borrow PCG, we must have an exclusive access to the
    /// corresponding place in the free PCG, e.g., obtaining "Write" capability
    /// to *_2 requires an exclusive capability to _2
    pub fn fpcg_condition<'b>(self, repacker: PlaceRepacker<'b, 'tcx>) -> Self {
        match self {
            Condition::Capability(place, kind) => {
                let fpcg_place = get_place_to_expand_to(place, repacker);
                let capability_kind = if place != fpcg_place {
                    CapabilityKind::Exclusive
                } else {
                    kind
                };
                Condition::Capability(fpcg_place, capability_kind)
            }
            _ => self,
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

        // For some reason the field projection may yield a different lifetime parameter
        // what is expected based on the ADT definition and substs.
        // We use the ADT definition because it will ensure that in the PCS the lifetime parameter
        // of all fields relates to the parameter of their parent struct.
        curr_place = curr_place
            .mk_place_elem(*elem, repacker)
            .with_inherent_region(repacker);
    }
    curr_place
}

pub(crate) struct TripleWalker<'a, 'tcx: 'a> {
    /// Evaluate all Operands/Rvalues
    pub(crate) operand_triples: Vec<Triple<'tcx>>,
    /// Evaluate all other statements/terminators
    pub(crate) main_triples: Vec<Triple<'tcx>>,
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
}

impl<'a, 'tcx> TripleWalker<'a, 'tcx> {
    pub(crate) fn new(repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            operand_triples: Vec::new(),
            main_triples: Vec::new(),
            repacker,
        }
    }
}
impl<'tcx> FallableVisitor<'tcx> for TripleWalker<'_, 'tcx> {
    fn visit_operand_fallable(
        &mut self,
        operand: &mir::Operand<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_operand_fallable(operand, location)?;
        let triple = match *operand {
            Operand::Copy(place) => Triple {
                pre: Condition::read(place),
                post: None,
            },
            Operand::Move(place) => Triple {
                pre: Condition::exclusive(place, self.repacker),
                post: Some(Condition::write(place)),
            },
            Operand::Constant(..) => return Ok(()),
        };
        self.operand_triples.push(triple);
        Ok(())
    }

    fn visit_rvalue_fallable(
        &mut self,
        rvalue: &mir::Rvalue<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_rvalue_fallable(rvalue, location)?;
        use Rvalue::*;
        let pre = match rvalue {
            Use(_)
            | Repeat(_, _)
            | ThreadLocalRef(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Aggregate(_, _)
            | ShallowInitBox(_, _) => return Ok(()),

            &Ref(_, kind, place) => match kind {
                BorrowKind::Shared => Condition::read(place),
                BorrowKind::Fake(..) => return Ok(()),
                BorrowKind::Mut { .. } => Condition::exclusive(place, self.repacker),
            },
            &RawPtr(mutbl, place) => {
                if mutbl.is_mut() {
                    Condition::exclusive(place, self.repacker)
                } else {
                    Condition::read(place)
                }
            }
            &Len(place) | &Discriminant(place) | &CopyForDeref(place) => Condition::read(place),
        };
        tracing::debug!("Pre: {pre:?}");
        self.operand_triples.push(Triple { pre, post: None });
        Ok(())
    }

    fn visit_statement_fallable(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.super_statement_fallable(statement, location)?;
        use StatementKind::*;
        let t = match statement.kind {
            Assign(box (place, ref rvalue)) => Triple {
                pre: Condition::write(place),
                post: rvalue.capability().map(|cap| Condition::new(place, cap)),
            },
            FakeRead(box (_, place)) => Triple {
                pre: Condition::read(place),
                post: None,
            },
            // Looking into `rustc` it seems that `PlaceMention` is effectively ignored.
            PlaceMention(_) => return Ok(()),
            SetDiscriminant { box place, .. } => Triple {
                pre: Condition::exclusive(place, self.repacker),
                post: None,
            },
            Deinit(box place) => Triple {
                pre: Condition::exclusive(place, self.repacker),
                post: Some(Condition::write(place)),
            },
            StorageLive(local) => Triple {
                pre: Condition::Unalloc(local),
                post: Some(Condition::AllocateOrDeallocate(local)),
            },
            StorageDead(local) => Triple {
                pre: Condition::AllocateOrDeallocate(local),
                post: Some(Condition::Unalloc(local)),
            },
            Retag(_, box place) => Triple {
                pre: Condition::exclusive(place, self.repacker),
                post: None,
            },
            _ => return Ok(()),
        };
        self.main_triples.push(t);
        if let Assign(box (_, Rvalue::Ref(_, kind, place))) = &statement.kind {
            let triple = match kind {
                BorrowKind::Shared => Triple {
                    pre: Condition::read(*place),
                    post: Some(Condition::read(*place)),
                },
                BorrowKind::Fake(..) => return Ok(()),
                BorrowKind::Mut { kind } => {
                    let post = if matches!(kind, MutBorrowKind::TwoPhaseBorrow) {
                        Some(Condition::read(*place))
                    } else {
                        Some(Condition::RemoveCapability((*place).into()))
                    };
                    Triple {
                        pre: Condition::exclusive(*place, self.repacker),
                        post,
                    }
                }
            };
            self.main_triples.push(triple);
        }
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_terminator_fallable(terminator, location)?;
        use TerminatorKind::*;
        let t = match &terminator.kind {
            Goto { .. }
            | SwitchInt { .. }
            | UnwindResume
            | UnwindTerminate(_)
            | Unreachable
            | CoroutineDrop
            | Assert { .. }
            | FalseEdge { .. }
            | FalseUnwind { .. } => return Ok(()),
            Return => Triple {
                pre: Condition::Return,
                post: Some(Condition::write(RETURN_PLACE)),
            },
            &Drop { place, .. } => Triple {
                pre: Condition::write(place),
                post: None,
            },
            &Call { destination, .. } => Triple {
                pre: Condition::write(destination),
                post: Some(Condition::exclusive(destination, self.repacker)),
            },
            &Yield { resume_arg, .. } => Triple {
                pre: Condition::write(resume_arg),
                post: Some(Condition::exclusive(resume_arg, self.repacker)),
            },
            InlineAsm { .. } => {
                return Err(PcgError::unsupported(PCGUnsupportedError::InlineAssembly));
            }
            _ => todo!("{terminator:?}"),
        };
        self.main_triples.push(t);
        Ok(())
    }

    fn visit_place_fallable(
        &mut self,
        _place: Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) -> Result<(), PcgError> {
        Ok(())
    }
}

trait ProducesCapability {
    fn capability(&self) -> Option<CapabilityKind>;
}

impl ProducesCapability for Rvalue<'_> {
    fn capability(&self) -> Option<CapabilityKind> {
        use Rvalue::*;
        match self {
            Ref(_, BorrowKind::Fake(_), _) => None,
            Use(_)
            | Repeat(_, _)
            | Ref(_, _, _)
            | RawPtr(_, _)
            | ThreadLocalRef(_)
            | Len(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Discriminant(_)
            | Aggregate(_, _)
            | CopyForDeref(_) => Some(CapabilityKind::Exclusive),
            ShallowInitBox(_, _) => Some(CapabilityKind::ShallowExclusive),
        }
    }
}
