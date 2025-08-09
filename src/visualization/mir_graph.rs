use crate::{
    rustc_interface,
    utils::{CompilerCtxt, Place, display::DisplayWithCompilerCtxt},
};
use serde_derive::Serialize;
use std::{
    fs::File,
    io::{self},
};

use rustc_interface::middle::mir::{
    self, BinOp, Local, Operand, Rvalue, Statement, TerminatorKind, UnwindAction,
};

#[rustversion::since(2025-03-02)]
use rustc_interface::middle::mir::RawPtrKind;

#[rustversion::before(2025-03-02)]
use rustc_interface::ast::Mutability;

#[derive(Serialize)]
struct MirGraph {
    nodes: Vec<MirNode>,
    edges: Vec<MirEdge>,
}

#[derive(Serialize)]
struct MirStmt {
    stmt: String,
    loans_invalidated_start: Vec<String>,
    loans_invalidated_mid: Vec<String>,
    borrows_in_scope_start: Vec<String>,
    borrows_in_scope_mid: Vec<String>,
}

#[derive(Serialize)]
struct MirNode {
    id: String,
    block: usize,
    stmts: Vec<MirStmt>,
    terminator: String,
}

#[derive(Serialize)]
struct MirEdge {
    source: String,
    target: String,
    label: String,
}

fn format_bin_op(op: &BinOp) -> String {
    match op {
        BinOp::Add => "+".to_string(),
        BinOp::Sub => "-".to_string(),
        BinOp::Mul => "*".to_string(),
        BinOp::Div => "/".to_string(),
        BinOp::Rem => "%".to_string(),
        BinOp::AddUnchecked => todo!(),
        BinOp::SubUnchecked => todo!(),
        BinOp::MulUnchecked => todo!(),
        BinOp::BitXor => "^".to_string(),
        BinOp::BitAnd => "&".to_string(),
        BinOp::BitOr => "|".to_string(),
        BinOp::Shl => "<<".to_string(),
        BinOp::ShlUnchecked => "<<".to_string(),
        BinOp::Shr => ">>".to_string(),
        BinOp::ShrUnchecked => ">>".to_string(),
        BinOp::Eq => "==".to_string(),
        BinOp::Lt => "<".to_string(),
        BinOp::Le => "<=".to_string(),
        BinOp::Ne => "!=".to_string(),
        BinOp::Ge => ">=".to_string(),
        BinOp::Gt => ">".to_string(),
        BinOp::Offset => todo!(),
        BinOp::Cmp => todo!(),
        BinOp::AddWithOverflow => "+".to_string(),
        BinOp::SubWithOverflow => "-".to_string(),
        BinOp::MulWithOverflow => "*".to_string(),
    }
}

fn format_local<'tcx>(local: &Local, repacker: CompilerCtxt<'_, 'tcx>) -> String {
    let place: Place<'tcx> = (*local).into();
    place.to_short_string(repacker)
}

fn format_place<'tcx>(place: &mir::Place<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> String {
    let place: Place<'tcx> = (*place).into();
    place.to_short_string(repacker)
}

fn format_operand<'tcx>(operand: &Operand<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> String {
    match operand {
        Operand::Copy(p) => format_place(p, repacker),
        Operand::Move(p) => format!("move {}", format_place(p, repacker)),
        Operand::Constant(c) => format!("{c}"),
    }
}

#[rustversion::since(2025-03-02)]
fn format_raw_ptr<'tcx>(
    kind: &RawPtrKind,
    place: &mir::Place<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> String {
    let kind = match kind {
        RawPtrKind::Mut => "mut",
        RawPtrKind::Const => "const",
        RawPtrKind::FakeForPtrMetadata => todo!(),
    };
    format!("*{} {}", kind, format_place(place, ctxt))
}

#[rustversion::before(2025-03-02)]
fn format_raw_ptr<'tcx>(
    kind: &Mutability,
    place: &mir::Place<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> String {
    let kind = match kind {
        Mutability::Mut => "mut",
        Mutability::Not => "const",
    };
    format!("*{} {}", kind, format_place(place, ctxt))
}

#[allow(unreachable_patterns)]
fn format_rvalue<'tcx>(rvalue: &Rvalue<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
    match rvalue {
        Rvalue::Use(operand) => format_operand(operand, ctxt),
        Rvalue::Repeat(operand, c) => format!("repeat {} {}", format_operand(operand, ctxt), c),
        Rvalue::Ref(_region, kind, place) => {
            let kind = match kind {
                mir::BorrowKind::Shared => "",
                mir::BorrowKind::Mut { .. } => "mut",
                mir::BorrowKind::Fake(_) => "fake",
            };
            format!("&{} {}", kind, format_place(place, ctxt))
        }
        Rvalue::RawPtr(kind, place) => format_raw_ptr(kind, place, ctxt),
        Rvalue::ThreadLocalRef(_) => todo!(),
        Rvalue::Len(x) => format!("len({})", format_place(x, ctxt)),
        Rvalue::Cast(_, operand, ty) => format!("{} as {}", format_operand(operand, ctxt), ty),
        Rvalue::BinaryOp(op, box (lhs, rhs)) => {
            format!(
                "{} {} {}",
                format_operand(lhs, ctxt),
                format_bin_op(op),
                format_operand(rhs, ctxt)
            )
        }
        Rvalue::NullaryOp(op, _) => format!("{op:?}"),
        Rvalue::UnaryOp(op, val) => {
            format!("{:?} {}", op, format_operand(val, ctxt))
        }
        Rvalue::Discriminant(place) => format!("Discriminant({})", format_place(place, ctxt)),
        Rvalue::Aggregate(kind, ops) => {
            format!(
                "Aggregate {:?} {}",
                kind,
                ops.iter()
                    .map(|op| format_operand(op, ctxt))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        Rvalue::ShallowInitBox(operand, _) => format!("Box({})", format_operand(operand, ctxt)),
        Rvalue::CopyForDeref(place) => format!("CopyForDeref({})", format_place(place, ctxt)),
        _ => todo!(),
    }
}
fn format_terminator<'tcx>(
    terminator: &TerminatorKind<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> String {
    match terminator {
        TerminatorKind::Drop {
            place,
            target,
            unwind,
            ..
        } => {
            format!(
                "drop({}) -> [return: {target:?}, unwind: {unwind:?}]",
                format_place(place, ctxt)
            )
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            target: _,
            unwind: _,
            call_source: _,
            fn_span: _,
        } => {
            format!(
                "{} = {}({})",
                format_place(destination, ctxt),
                format_operand(func, ctxt),
                args.iter()
                    .map(|arg| format_operand(&arg.node, ctxt))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        _ => format!("{terminator:?}"),
    }
}

fn format_stmt<'tcx>(stmt: &Statement<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> String {
    match &stmt.kind {
        mir::StatementKind::Assign(box (place, rvalue)) => {
            format!(
                "{} = {}",
                format_place(place, repacker),
                format_rvalue(rvalue, repacker)
            )
        }
        mir::StatementKind::FakeRead(box (_, place)) => {
            format!("FakeRead({})", format_place(place, repacker))
        }
        mir::StatementKind::SetDiscriminant {
            place,
            variant_index,
        } => format!(
            "SetDiscriminant({} {:?})",
            format_place(place, repacker),
            variant_index
        ),
        mir::StatementKind::Deinit(_) => todo!(),
        mir::StatementKind::StorageLive(local) => {
            format!("StorageLive({})", format_local(local, repacker))
        }
        mir::StatementKind::StorageDead(local) => {
            format!("StorageDead({})", format_local(local, repacker))
        }
        mir::StatementKind::Retag(_, _) => todo!(),
        mir::StatementKind::PlaceMention(place) => {
            format!("PlaceMention({})", format_place(place, repacker))
        }
        mir::StatementKind::AscribeUserType(_, _) => "AscribeUserType(...)".to_string(),
        mir::StatementKind::Coverage(_) => "coverage".to_string(),
        mir::StatementKind::Intrinsic(non_diverging_intrinsic) => {
            format!("Intrinsic({:?})", non_diverging_intrinsic)
        }
        mir::StatementKind::ConstEvalCounter => todo!(),
        mir::StatementKind::Nop => todo!(),
        _ => todo!(),
    }
}

fn mk_mir_graph(ctxt: CompilerCtxt<'_, '_>) -> MirGraph {
    let mut nodes = Vec::new();
    let mut edges = Vec::new();

    let location_table = ctxt.bc.rust_borrow_checker().unwrap().location_table();
    for (bb, data) in ctxt.body().basic_blocks.iter_enumerated() {
        let stmts = data.statements.iter().enumerate().map(|(idx, stmt)| {
            let stmt = format_stmt(stmt, ctxt);
            let bc = ctxt.bc.rust_borrow_checker().unwrap();
            let invalidated_at = &bc.input_facts().loan_invalidated_at;
            let location = mir::Location {
                block: bb,
                statement_index: idx,
            };
            let loans_invalidated_start = invalidated_at
                .iter()
                .filter_map(|(point, idx)| {
                    if *point == location_table.start_index(location) {
                        let borrow_region = bc.borrow_index_to_region(*idx);
                        Some(format!("{borrow_region:?}"))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            let loans_invalidated_mid = invalidated_at
                .iter()
                .filter_map(|(point, idx)| {
                    if *point == location_table.mid_index(location) {
                        let borrow_region = bc.borrow_index_to_region(*idx);
                        Some(format!("{borrow_region:?}"))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            let borrows_in_scope_start = bc
                .borrows_in_scope_at(location, true)
                .iter()
                .map(|bi| format!("{bi:?}"))
                .collect::<Vec<_>>();
            let borrows_in_scope_mid = bc
                .borrows_in_scope_at(location, false)
                .iter()
                .map(|bi| format!("{bi:?}"))
                .collect::<Vec<_>>();
            MirStmt {
                stmt,
                loans_invalidated_start,
                loans_invalidated_mid,
                borrows_in_scope_start,
                borrows_in_scope_mid,
            }
        });

        let terminator = format_terminator(&data.terminator().kind, ctxt);

        nodes.push(MirNode {
            id: format!("{bb:?}"),
            block: bb.as_usize(),
            stmts: stmts.collect(),
            terminator,
        });

        match &data.terminator().kind {
            TerminatorKind::Goto { target } => {
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{target:?}"),
                    label: "goto".to_string(),
                });
            }
            TerminatorKind::SwitchInt { discr: _, targets } => {
                for (val, target) in targets.iter() {
                    edges.push(MirEdge {
                        source: format!("{bb:?}"),
                        target: format!("{target:?}"),
                        label: format!("{val}"),
                    });
                }
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{:?}", targets.otherwise()),
                    label: "otherwise".to_string(),
                });
            }
            TerminatorKind::UnwindResume => {}
            TerminatorKind::UnwindTerminate(_) => todo!(),
            TerminatorKind::Return => {}
            TerminatorKind::Unreachable => {}
            TerminatorKind::Drop { target, .. } => {
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{target:?}"),
                    label: "drop".to_string(),
                });
            }
            TerminatorKind::Call {
                func: _,
                args: _,
                destination: _,
                target,
                unwind,
                call_source: _,
                fn_span: _,
            } => {
                if let Some(target) = target {
                    edges.push(MirEdge {
                        source: format!("{bb:?}"),
                        target: format!("{target:?}"),
                        label: "call".to_string(),
                    });
                    match unwind {
                        UnwindAction::Continue => todo!(),
                        UnwindAction::Unreachable => todo!(),
                        UnwindAction::Terminate(_) => todo!(),
                        UnwindAction::Cleanup(cleanup) => {
                            edges.push(MirEdge {
                                source: format!("{bb:?}"),
                                target: format!("{cleanup:?}"),
                                label: "unwind".to_string(),
                            });
                        }
                    }
                }
            }
            TerminatorKind::Assert {
                cond: _,
                expected: _,
                msg: _,
                target,
                unwind,
            } => {
                match unwind {
                    UnwindAction::Continue => todo!(),
                    UnwindAction::Unreachable => todo!(),
                    UnwindAction::Terminate(_) => todo!(),
                    UnwindAction::Cleanup(cleanup) => {
                        edges.push(MirEdge {
                            source: format!("{bb:?}"),
                            target: format!("{cleanup:?}"),
                            label: "unwind".to_string(),
                        });
                    }
                }
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{target:?}"),
                    label: "success".to_string(),
                });
            }
            TerminatorKind::Yield {
                value: _,
                resume: _,
                resume_arg: _,
                drop: _,
            } => todo!(),
            TerminatorKind::FalseEdge {
                real_target,
                imaginary_target: _,
            } => {
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{real_target:?}"),
                    label: "real".to_string(),
                });
            }
            TerminatorKind::FalseUnwind {
                real_target,
                unwind: _,
            } => {
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{real_target:?}"),
                    label: "real".to_string(),
                });
            }
            TerminatorKind::InlineAsm { .. } => todo!(),
            TerminatorKind::CoroutineDrop => todo!(),
            _ => todo!(),
        }
    }

    MirGraph { nodes, edges }
}
pub(crate) fn generate_json_from_mir(path: &str, ctxt: CompilerCtxt<'_, '_>) -> io::Result<()> {
    let mir_graph = mk_mir_graph(ctxt);
    let mut file = File::create(path)?;
    serde_json::to_writer(&mut file, &mir_graph)?;
    Ok(())
}
