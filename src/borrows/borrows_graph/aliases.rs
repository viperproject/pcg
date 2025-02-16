use derive_more::From;
use egg::{define_language, EGraph, Id, Language};

use crate::{
    borrows::{
        borrow_pcg_edge::BorrowPCGEdgeRef, borrow_pcg_expansion::BorrowPCGExpansion,
        edge::kind::BorrowPCGEdgeKind, region_projection::RegionIdx,
        region_projection_member::RegionProjectionMemberKind,
    },
    combined_pcs::PCGNode,
    rustc_interface::data_structures::fx::FxHashSet,
    utils::{display::DisplayWithRepacker, PlaceRepacker},
};

use super::BorrowsGraph;
use crate::borrows::{
    borrow_pcg_edge::BorrowPCGEdgeLike, edge_data::EdgeData, region_projection::RegionProjection,
};
use egg::*;

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
    pub(crate) fn aliases(
        &self,
        node: PCGNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        let mut seen = FxHashSet::default();
        let mut graph: EGraph<EggPcgNode, ()> = EGraph::new(());
        let mut place_ids: Vec<PCGNode<'tcx>> = vec![];

        fn get_node<'tcx>(place: PCGNode<'tcx>, place_ids: &mut Vec<PCGNode<'tcx>>) -> EggPcgNode {
            for (idx, place_id) in place_ids.iter().enumerate() {
                if place_id == &place {
                    return EggPcgNode::Node(idx);
                }
            }
            place_ids.push(place);
            EggPcgNode::Node(place_ids.len() - 1)
        }

        seen.insert(node);
        graph.add(get_node(node, &mut place_ids));

        // Helper function to recursively collect places
        fn collect_nodes_up<'tcx>(
            graph: &BorrowsGraph<'tcx>,
            node: PCGNode<'tcx>,
            egraph: &mut EGraph<EggPcgNode, ()>,
            seen: &mut FxHashSet<PCGNode<'tcx>>,
            place_ids: &mut Vec<PCGNode<'tcx>>,
            repacker: PlaceRepacker<'_, 'tcx>,
        ) {
            let blocking_node = egraph.add(get_node(node, place_ids));
            // Add places from blocked nodes
            if let Some(local_node) = node.as_local_node() {
                for edge in graph.edges_blocked_by(local_node, repacker) {
                    let blocked_nodes = match edge.kind() {
                        BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => {
                            vec![expansion.base().into()].into_iter().collect()
                        }
                        _ => edge.blocked_nodes(repacker),
                    };
                    for blocked in blocked_nodes {
                        if seen.insert(blocked) {
                            // eprintln!(
                            //     "up: {} -> {}",
                            //     node.to_short_string(repacker),
                            //     blocked.to_short_string(repacker)
                            // );
                            let blocked_node = egraph.add(get_node(blocked, place_ids));
                            add_to_egraph(blocked_node, blocking_node, edge, egraph);
                            collect_nodes_up(graph, blocked, egraph, seen, place_ids, repacker);
                        }
                    }
                }
            }
        }

        fn record_deref(blocked_node: Id, blocking_node: Id, egraph: &mut EGraph<EggPcgNode, ()>) {
            // *blocked = blocking node
            let deref_blocked = egraph.add(EggPcgNode::Deref(blocked_node));
            egraph.union(deref_blocked, blocking_node);

            // &blocking = blocked node
            let ref_blocking = egraph.add(EggPcgNode::Ref(blocking_node));
            egraph.union(ref_blocking, blocked_node);
        }

        fn add_to_egraph<'tcx>(
            blocked_node: Id,
            blocking_node: Id,
            edge: BorrowPCGEdgeRef<'tcx, '_>,
            egraph: &mut EGraph<EggPcgNode, ()>,
        ) {
            match edge.kind() {
                BorrowPCGEdgeKind::RegionProjectionMember(projection) => match projection.kind {
                    RegionProjectionMemberKind::DerefRegionProjection => {
                        egraph.union(blocked_node, blocking_node);
                    }
                    RegionProjectionMemberKind::Ref => {
                        egraph.union(blocked_node, blocking_node);
                    }
                    // RegionProjectionMemberKind::Aggregate {
                    //     field_idx,
                    //     target_rp_index,
                    // } => todo!(),
                    // RegionProjectionMemberKind::Borrow => todo!(),
                    // RegionProjectionMemberKind::FunctionInput => todo!(),
                    // RegionProjectionMemberKind::Todo => {
                    _ => {
                        // We don't know exactly how these nodes are related.
                        // We conservatively assume various relations between blocked and blocking nodes
                        // TODO: This can be made much more precise
                        record_deref(blocked_node, blocking_node, egraph);
                        record_deref(blocking_node, blocked_node, egraph);
                        egraph.union(blocked_node, blocking_node);
                    }
                },
                BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => match expansion {
                    BorrowPCGExpansion::FromOwned(_) => {
                        record_deref(blocked_node, blocking_node, egraph)
                    }
                    BorrowPCGExpansion::FromBorrow(e) => {
                        if e.expansion.is_deref() {
                            record_deref(blocked_node, blocking_node, egraph);
                        } else {
                            egraph.union(blocked_node, blocking_node);
                        }
                    }
                },
                _ => {
                    egraph.union(blocked_node, blocking_node);
                }
            }
        }

        fn collect_nodes_down<'tcx>(
            graph: &BorrowsGraph<'tcx>,
            node: PCGNode<'tcx>,
            egraph: &mut EGraph<EggPcgNode, ()>,
            seen: &mut FxHashSet<PCGNode<'tcx>>,
            place_ids: &mut Vec<PCGNode<'tcx>>,
            repacker: PlaceRepacker<'_, 'tcx>,
        ) {
            let blocked_id = egraph.add(get_node(node, place_ids));

            for edge in graph.edges_blocking(node, repacker) {
                for blocking in edge.blocked_by_nodes(repacker) {
                    let node: PCGNode<'tcx> = blocking.into();
                    if seen.insert(node) {
                        let blocking_id = egraph.add(get_node(node, place_ids));
                        add_to_egraph(blocking_id, blocked_id, edge, egraph);
                        collect_nodes_down(graph, node, egraph, seen, place_ids, repacker);
                    }
                }
            }
        }

        collect_nodes_up(
            self,
            node.into(),
            &mut graph,
            &mut seen,
            &mut place_ids,
            repacker,
        );

        collect_nodes_down(
            self,
            node.into(),
            &mut graph,
            &mut seen,
            &mut place_ids,
            repacker,
        );

        graph.rebuild();
        let mut result = FxHashSet::default();
        let canonical_id = graph.lookup(get_node(node, &mut place_ids)).unwrap();
        for node in seen {
            let node_id = graph.lookup(get_node(node, &mut place_ids));
            // eprintln!("{} -> {}", node.to_short_string(repacker), node_id.unwrap());
            if node_id == Some(canonical_id) {
                result.insert(node);
            }
        }

        if let Some(place) = node.as_current_place()
            && place.is_deref()
        {
            let ref_place = place.last_projection().unwrap().0;
            if let Some(ref_region) = ref_place.get_ref_region(repacker) {
                let rp = RegionProjection::new(ref_region, ref_place, repacker);
                let aliases = self.aliases(rp.into(), repacker);
                result.extend(aliases);
            }
        }

        result
    }
}

#[cfg(test)]
#[test]
fn test_aliases() {
    use rustc_utils::test_utils::Placer;

    use crate::rustc_interface::middle::mir::{self, START_BLOCK};

    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();

    use crate::run_combined_pcs;

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
        let bb = pcg.get_all_for_bb((3 as usize).into());
        let stmt = &bb.statements[8];
        let temp: mir::Place<'_> = mir::Local::from(19 as usize).into();
        let star_temp = temp.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let repacker = PlaceRepacker::new(&body.body, tcx);
        assert!(!stmt
            .aliases(star_temp.into(), repacker)
            .contains(&temp.into()));
    });

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
        let bb0 = pcg.get_all_for_bb(START_BLOCK);
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
        let bb0 = pcg.get_all_for_bb(START_BLOCK);
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
        let bb0 = pcg.get_all_for_bb(START_BLOCK);
        let last_bg = &bb0.statements[13];
        let temp: mir::Place<'_> = mir::Local::from(5 as usize).into();
        let star_5 = temp.project_deeper(&[mir::ProjectionElem::Deref], tcx);
        let repacker = PlaceRepacker::new(&body.body, tcx);
        let x = placer.local("x").mk();
        assert!(last_bg.aliases(star_5.into(), repacker).contains(&x.into()));
    });
}
