use egg::{define_language, EGraph, Id};

use crate::{
    borrows::{
        borrow_pcg_edge::{BorrowPCGEdgeRef, LocalNode},
        borrow_pcg_expansion::BorrowPCGExpansion,
        edge::kind::BorrowPCGEdgeKind,
        region_projection::RegionIdx,
        region_projection_member::RegionProjectionMemberKind,
    },
    combined_pcs::{LocalNodeLike, PCGNode, PCGNodeLike},
    rustc_interface::{data_structures::fx::FxHashSet, middle::mir::PlaceElem},
    utils::{display::DisplayWithRepacker, HasPlace, Place, PlaceRepacker},
};

use super::BorrowsGraph;
use crate::borrows::{
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

impl<'tcx> BorrowsGraph<'tcx> {
    #[tracing::instrument(skip(repacker))]
    pub(crate) fn aliases(
        &self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        let mut result = FxHashSet::default();

        for (place, proj) in node.iter_projections(repacker) {
            let mut curr_aliases: FxHashSet<PCGNode<'tcx>> = FxHashSet::default();
            curr_aliases.insert(place.into());
            curr_aliases.extend(result.drain());
            for alias in curr_aliases {
                if matches!(proj, PlaceElem::Deref)
                    && let PCGNode::Place(p) = place
                    && let Some(rp) = p.base_region_projection(repacker)
                {
                    result.extend(self.direct_aliases(
                        rp.to_local_node(),
                        repacker,
                        &mut FxHashSet::default(),
                    ));
                }
                let projected = alias
                    .as_local_node()
                    .unwrap()
                    .project_deeper(repacker, proj);
                result.insert(projected.into());
                if projected != node {
                    let aliases = self.aliases(projected, repacker);
                    result.extend(aliases);
                }
            }
        }
        result
    }

    fn direct_aliases(
        &self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        seen: &mut FxHashSet<PCGNode<'tcx>>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        let mut result = FxHashSet::default();

        let extend = |blocked: PCGNode<'tcx>,
                      seen: &mut FxHashSet<PCGNode<'tcx>>,
                      result: &mut FxHashSet<PCGNode<'tcx>>| {
            if seen.insert(blocked.into()) {
                result.insert(blocked.into());
                if let Some(local_node) = blocked.try_to_local_node() {
                    result.extend(self.direct_aliases(local_node.into(), repacker, seen));
                }
            }
        };

        for edge in self.edges_blocked_by(node, repacker) {
            match edge.kind {
                BorrowPCGEdgeKind::Borrow(borrow_edge) => {
                    let blocked = borrow_edge.blocked_place;
                    extend(blocked.into(), seen, &mut result);
                }
                BorrowPCGEdgeKind::BorrowPCGExpansion(e) => {
                    if !e.is_owned_expansion() {
                        extend(e.base().into(), seen, &mut result);
                    }
                }
                BorrowPCGEdgeKind::Abstraction(abstraction_type) => {
                    for edge in abstraction_type.edges() {
                        for input in edge.inputs() {
                            extend(input.to_pcg_node(), seen, &mut result);
                        }
                    }
                }
                BorrowPCGEdgeKind::RegionProjectionMember(region_projection_member) => {
                    match &region_projection_member.kind {
                        RegionProjectionMemberKind::DerefRegionProjection => {
                            for input in region_projection_member.inputs() {
                                extend(input.to_pcg_node(), seen, &mut result);
                            }
                        }
                        _ => {}
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

    use crate::free_pcs::FreePcsLocation;
    use crate::rustc_interface::middle::mir::{self, START_BLOCK};

    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();

    use crate::{run_combined_pcs, FpcsOutput};

    fn check_all_statements<'mir, 'tcx>(
        body: &'mir mir::Body<'tcx>,
        pcg: &mut FpcsOutput<'mir, 'tcx>,
        f: impl Fn(mir::Location, &FreePcsLocation<'tcx>),
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
            fn main() {
                let mut x: i32 = 1;
                let mut y = &mut x;
                let z = &mut y;
                let w = &mut **z;
                *w = 2;
                *y;
            }
        });
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
            let _ = stmt.aliases(x.into(), repacker);
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
                    .aliases(star_temp.into(), repacker)
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
                    .aliases(deref_temp_9.into(), repacker)
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
            .aliases(e_deref.into(), repacker)
            .contains(&a.into()));
        assert!(last_bg
            .all_place_aliases(repacker)
            .get(e_deref.into(), tcx)
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
            .aliases(starstarc.into(), repacker)
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
            .aliases(star_yyy.into(), repacker)
            .contains(&x.into()));
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
        assert!(last_bg.aliases(star_5.into(), repacker).contains(&x.into()));
    });
}
