use egg::{define_language, EGraph, Id};

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeRef, LocalNode},
        borrow_pcg_expansion::BorrowPCGExpansion,
        edge::kind::BorrowPCGEdgeKind,
        region_projection::RegionIdx,
        region_projection_member::RegionProjectionMemberKind,
    },
    combined_pcs::{LocalNodeLike, PCGNode, PCGNodeLike},
    rustc_interface::{data_structures::fx::FxHashSet, middle::mir::PlaceElem, span::Symbol},
    utils::{display::DisplayWithRepacker, HasPlace, Place, PlaceRepacker},
};

use super::BorrowsGraph;
use crate::borrow_pcg::{
    borrow_pcg_edge::BorrowPCGEdgeLike, edge_data::EdgeData, region_projection::RegionProjection,
};

define_language! {
    enum EggPcgNode {
        Node(usize),
        "*" = Deref(Id),
        "&" = Ref(Id),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PCGNodeDiscriminant {
    Place,
    RegionProjection(RegionIdx),
    Const,
}

#[derive(Eq, PartialEq, Hash)]
struct Alias<'tcx> {
    node: PCGNode<'tcx>,
    exact_alias: bool,
}

impl<'tcx> BorrowsGraph<'tcx> {
    #[tracing::instrument(skip(repacker))]
    pub(crate) fn aliases(
        &self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        let mut results: FxHashSet<Alias<'tcx>> = FxHashSet::default();
        for (place, proj) in node.iter_projections(repacker) {
            results.insert(Alias {
                node: place.into(),
                exact_alias: true,
            });
            let candidates: Vec<_> = results.drain().collect();
            for alias in candidates {
                if !alias.exact_alias {
                    continue;
                }
                let local_node = if let Some(local_node) = alias.node.try_to_local_node() {
                    local_node
                } else {
                    continue;
                };
                let local_node = if let Some(n) = local_node.project_deeper(repacker, proj) {
                    n
                } else {
                    continue;
                };
                results.extend(self.direct_aliases(
                    local_node,
                    repacker,
                    &mut FxHashSet::default(),
                    true,
                ));
                match local_node {
                    PCGNode::Place(p) => {
                        if let Some(rp) = p.deref_to_rp(repacker) {
                            results.extend(self.direct_aliases(
                                rp.try_to_local_node().unwrap().into(),
                                repacker,
                                &mut FxHashSet::default(),
                                true,
                            ));
                        }
                    }
                    _ => {}
                }
            }
        }
        results.into_iter().map(|a| a.node).collect()
    }

    fn direct_aliases(
        &self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        seen: &mut FxHashSet<PCGNode<'tcx>>,
        direct: bool,
    ) -> FxHashSet<Alias<'tcx>> {
        let mut result = FxHashSet::default();
        result.insert(Alias {
            node: node.into(),
            exact_alias: direct,
        });

        let extend = |blocked: PCGNode<'tcx>,
                      seen: &mut FxHashSet<PCGNode<'tcx>>,
                      result: &mut FxHashSet<Alias<'tcx>>,
                      exact_alias: bool| {
            if seen.insert(blocked.into()) {
                result.insert(Alias {
                    node: blocked,
                    exact_alias,
                });
                if let Some(local_node) = blocked.try_to_local_node() {
                    result.extend(self.direct_aliases(
                        local_node.into(),
                        repacker,
                        seen,
                        exact_alias,
                    ));
                }
            }
        };

        for edge in self.edges_blocked_by(node, repacker) {
            match edge.kind {
                BorrowPCGEdgeKind::Borrow(borrow_edge) => {
                    let blocked = borrow_edge.blocked_place;
                    extend(blocked.into(), seen, &mut result, direct);
                }
                BorrowPCGEdgeKind::BorrowPCGExpansion(e) => match e.base() {
                    PCGNode::Place(_) => {}
                    PCGNode::RegionProjection(region_projection) => {
                        extend(region_projection.into(), seen, &mut result, false);
                    }
                },
                BorrowPCGEdgeKind::Abstraction(abstraction_type) => {
                    for edge in abstraction_type.edges() {
                        for input in edge.inputs() {
                            extend(input.to_pcg_node(), seen, &mut result, false);
                        }
                    }
                }
                BorrowPCGEdgeKind::RegionProjectionMember(region_projection_member) => {
                    match &region_projection_member.kind {
                        RegionProjectionMemberKind::DerefRegionProjection => {
                            for input in region_projection_member.inputs() {
                                extend(input.to_pcg_node(), seen, &mut result, direct);
                            }
                        }
                        RegionProjectionMemberKind::DerefBorrowOutlives => {}
                        _ => {
                            for input in region_projection_member.inputs() {
                                extend(input.to_pcg_node(), seen, &mut result, false);
                            }
                        }
                    }
                }
            }
        }
        result
    }
}

#[cfg(test)]
#[test]
fn test_aliases() {
    use rustc_utils::test_utils::Placer;

    use crate::free_pcs::PcgLocation;
    use crate::rustc_interface::middle::mir::{self, START_BLOCK};

    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();

    use crate::{run_combined_pcs, FpcsOutput};

    fn check_all_statements<'mir, 'tcx>(
        body: &'mir mir::Body<'tcx>,
        pcg: &mut FpcsOutput<'mir, 'tcx>,
        f: impl Fn(mir::Location, &PcgLocation<'tcx>),
    ) {
        for block in body.basic_blocks.indices() {
            let stmts_option = pcg.get_all_for_bb(block).unwrap();
            let stmts = if let Some(stmts) = stmts_option {
                stmts
            } else {
                continue;
            };
            for (i, stmt) in stmts.statements.iter().enumerate() {
                let location = mir::Location {
                    block,
                    statement_index: i,
                };
                f(location, stmt);
            }
        }
    }

    // enum_write_branch_read_whole
    let input = r#"
    fn main() {
    enum Foo {
        X(i32),
        Y(i32),
    }
    let mut x = Foo::X(1);
    if let Foo::X(z) = &mut x {
        *z += 1;
    }
    if let Foo::Y(z) = &mut x {
        *z += 1;
    }
    x;
    }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let mut pcg = run_combined_pcs(body, tcx, None);
        let bb = pcg.get_all_for_bb(3usize.into()).unwrap().unwrap();
        let stmt = &bb.statements[0];
        let init_z: mir::Place<'_> = mir::Local::from(5 as usize).into();
        let z_deref = init_z.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let repacker = PlaceRepacker::new(&body.body, tcx);
        let local3: mir::Place<'_> = mir::Local::from(3 as usize).into();
        let deref3 = local3.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let deref_target = deref3.project_deeper(
            &[
                mir::ProjectionElem::Downcast(Some(Symbol::intern(&"X")), 0usize.into()),
                mir::ProjectionElem::Field(0usize.into(), tcx.types.i32),
            ],
            tcx,
        );
        let aliases = stmt.aliases(z_deref, &body.body, tcx);
        eprintln!("aliases: {:?}", aliases);
        eprintln!("deref_target: {:?}", deref_target);
        assert!(aliases.contains(&deref_target.into()));
        assert!(!aliases.contains(&deref3.into()));
    });

    // 59_struct_ptrs_deep.rs
    let input = r#"
    struct A(i32);
    struct B<'a>(&'a A);
    struct C<'a, 'b>(&'b B<'a>);
    struct D<'a, 'b, 'c>(&'c C<'a, 'b>);

    fn foo() {
        let x = D(&C(&B(&A(0))));
        let y = x.0 .0 .0 .0 + 1;
    }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let mut pcg = run_combined_pcs(body, tcx, None);
        let placer = Placer::new(tcx, &body.body);
        let x = placer.local("x").mk();
        let repacker = PlaceRepacker::new(&body.body, tcx);
        check_all_statements(&body.body, &mut pcg, |location, stmt| {
            let _ = stmt.aliases(x, &body.body, tcx);
            // assert!(
            //     !stmt
            //         .aliases(star_temp.into(), repacker)
            //         .contains(&temp.into()),
            //     "Bad alias for {:?}",
            //     location
            // );
        });
    });

    let input = r#"
fn main() {
    struct Foo<'a>(&'a mut i32);
    let mut x = 1;
    let f = Foo(&mut x);
    *f.0 += 1;
    x;
}
"#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let mut pcg = run_combined_pcs(body, tcx, None);
        let temp: mir::Place<'_> = mir::Local::from(4 as usize).into();
        let star_temp = temp.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let repacker = PlaceRepacker::new(&body.body, tcx);
        check_all_statements(&body.body, &mut pcg, |location, stmt| {
            assert!(
                !stmt
                    .aliases(star_temp, &body.body, tcx)
                    .contains(&temp.into()),
                "Bad alias for {:?}",
                location
            );
        });
    });

    let input = r#"
            fn main() {
                use std::time::Instant;
                fn run_expensive_calculation(){}
                let start = Instant::now();
                run_expensive_calculation();
                let elapsed = start.elapsed();
                println!("Elapsed: {}s", elapsed.as_secs());
            }"#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let mut pcg = run_combined_pcs(body, tcx, None);
        let temp_9: mir::Place<'_> = mir::Local::from(9 as usize).into();
        let deref_temp_9 = temp_9.project_deeper(&[mir::ProjectionElem::Deref], tcx);

        let temp_19: mir::Place<'_> = mir::Local::from(19 as usize).into();

        let repacker = PlaceRepacker::new(&body.body, tcx);
        check_all_statements(&body.body, &mut pcg, |location, stmt| {
            assert!(
                !stmt
                    .aliases(deref_temp_9, &body.body, tcx)
                    .contains(&temp_19.into()),
                "Bad alias for {:?}",
                location
            );
        });
    });

    // From flowistry_basic.rs
    let input = r#"
    fn main() {
      fn foo<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32 { x }

      let a = 1;
      let b = 2;
      let c = &a;
      let d = &b;
      let e = foo(c, d);
    }"#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let mut pcg = run_combined_pcs(body, tcx, None);
        let placer = Placer::new(tcx, &body.body);
        let bb0 = pcg.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = bb0.statements.last().unwrap();
        let e_deref = placer.local("e").deref().mk();
        let repacker = PlaceRepacker::new(&body.body, tcx);
        let a = placer.local("a").mk();
        assert!(last_bg
            .aliases(e_deref, &body.body, tcx)
            .contains(&a.into()));
    });

    // deep2
    let input = r#"
        fn foo() {
            let mut a = 1;
            let mut b  = &mut a;
            let mut c = &mut b;
            let d = **c;
        }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let mut pcg = run_combined_pcs(body, tcx, None);
        let placer = Placer::new(tcx, &body.body);
        let bb0 = pcg.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = &bb0.statements[10];
        let starstarc = placer.local("c").deref().deref().mk();
        let repacker = PlaceRepacker::new(&body.body, tcx);
        let a = placer.local("a").mk();
        assert!(last_bg
            .aliases(starstarc, &body.body, tcx)
            .contains(&a.into()));
    });

    // flowistry_pointer_deep
    let input = r#"
        fn foo() {
            let x = 1;
            let y = &&&x;
            let a = ***y;
        }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let mut pcg = run_combined_pcs(body, tcx, None);
        let placer = Placer::new(tcx, &body.body);
        let bb0 = pcg.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = &bb0.statements[11];
        let star_yyy = placer.local("y").deref().deref().deref().mk();
        let repacker = PlaceRepacker::new(&body.body, tcx);
        let x = placer.local("x").mk();
        assert!(last_bg
            .aliases(star_yyy, &body.body, tcx)
            .contains(&x.into()));
        assert!(!last_bg
            .aliases(star_yyy, &body.body, tcx)
            .contains(&mir::Local::from(3usize).into()));
    });

    let input = r#"
        fn main() {
            fn other(x: &mut i32, y: i32, z: i32) { *x += y; }
            let mut x = 1;
            let y = 1;
            let z = 1;
            other(&mut x, y, z);
            (x);
        }
    "#;
    rustc_utils::test_utils::compile_body(input, |tcx, _, body| {
        let mut pcg = run_combined_pcs(body, tcx, None);
        let placer = Placer::new(tcx, &body.body);
        let bb0 = pcg.get_all_for_bb(START_BLOCK).unwrap().unwrap();
        let last_bg = &bb0.statements[13];
        let temp: mir::Place<'_> = mir::Local::from(5 as usize).into();
        let star_5 = temp.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let repacker = PlaceRepacker::new(&body.body, tcx);
        let x = placer.local("x").mk();
        assert!(last_bg.aliases(star_5, &body.body, tcx).contains(&x.into()));
    });
}
