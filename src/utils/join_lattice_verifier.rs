use super::{display::{DebugLines, DisplayDiff}, CompilerCtxt};
use crate::rustc_interface::middle::mir;

/// `JoinLatticeVerifier` is used to detect correctness violations of the `join`
/// operation on a domain of type `T`, based on recorded join computations.
///
/// Currently, the verifier can detect certain cases when the invariants
/// `join(a, b) ≤ a` and `join(a, b) ≤ b` are violated. This is checked by
/// storing elements of `T` in a graph, where, for all recorded computations of
/// the form `join(a, b) = c`, there is an edge `a` -> `c` with weight `b` if `a != c` and there
/// is an edge `b` -> `c` with weight `a` if `b != c`.  If the join operation is implemented
/// correctly, then if an edge `a` can reach a distinct edge `b`, then a < b.
/// Conversely, if the graph forms a cycle, the join operation is not implemented
/// correctly, with the cycle being a counterexample.
#[derive(Debug, Clone)]
pub(crate) struct JoinLatticeVerifier<T> {
    #[allow(dead_code)]
    graph: petgraph::Graph<T, T>,
}

#[allow(unused)]
pub(crate) struct JoinComputation<T> {
    pub(crate) lhs: T,
    pub(crate) rhs: T,
    pub(crate) result: T,
}

pub(crate) trait HasBlock {
    fn block(&self) -> mir::BasicBlock;
}

impl<T: Clone + PartialEq + std::fmt::Debug> JoinLatticeVerifier<T> {
    #[allow(dead_code)]
    pub(crate) fn new() -> Self {
        Self {
            graph: petgraph::Graph::new(),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn record_join_result<'mir, 'tcx>(
        &mut self,
        computation: JoinComputation<T>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) where
        T: DebugLines<CompilerCtxt<'mir, 'tcx>> + HasBlock,
    {
        // Add nodes if they don't exist
        let lhs_idx = self.get_or_add_node(computation.lhs.clone());
        let rhs_idx = self.get_or_add_node(computation.rhs.clone());
        let result_idx = self.get_or_add_node(computation.result.clone());

        // Add edges from inputs to result with weights being the other operand
        if lhs_idx != result_idx {
            self.graph
                .add_edge(lhs_idx, result_idx, computation.rhs.clone());
        }
        if rhs_idx != result_idx {
            self.graph
                .add_edge(rhs_idx, result_idx, computation.lhs.clone());
        }

        use std::collections::HashSet;

        // For each node, try to find a cycle starting from it
        for start in self.graph.node_indices() {
            let mut visited = HashSet::new();
            let mut stack = vec![];
            let mut on_stack = HashSet::new();
            let mut edge_stack = vec![];

            #[allow(clippy::type_complexity)]
            fn dfs<T: Clone + PartialEq + std::fmt::Debug>(
                graph: &petgraph::Graph<T, T>,
                node: petgraph::graph::NodeIndex,
                visited: &mut HashSet<petgraph::graph::NodeIndex>,
                stack: &mut Vec<petgraph::graph::NodeIndex>,
                edge_stack: &mut Vec<T>,
                on_stack: &mut HashSet<petgraph::graph::NodeIndex>,
            ) -> Option<(Vec<(petgraph::graph::NodeIndex, T)>, Vec<T>)> {
                if on_stack.contains(&node) {
                    // Found cycle. Collect nodes from the cycle
                    let cycle_start_idx = stack.iter().position(|&x| x == node).unwrap();
                    let cycle: Vec<_> = stack[cycle_start_idx..]
                        .iter()
                        .map(|&idx| (idx, graph[idx].clone()))
                        .collect();
                    let weights = edge_stack[cycle_start_idx..].to_vec();
                    return Some((cycle, weights));
                }

                if visited.contains(&node) {
                    return None;
                }

                visited.insert(node);
                on_stack.insert(node);
                stack.push(node);

                for neighbor in graph.neighbors(node) {
                    let edge_weight = graph
                        .edge_weight(graph.find_edge(node, neighbor).unwrap())
                        .unwrap()
                        .clone();
                    edge_stack.push(edge_weight);
                    if let Some(cycle) = dfs(graph, neighbor, visited, stack, edge_stack, on_stack)
                    {
                        return Some(cycle);
                    }
                    edge_stack.pop();
                }

                stack.pop();
                on_stack.remove(&node);
                None
            }

            if let Some((cycle, weights)) = dfs(
                &self.graph,
                start,
                &mut visited,
                &mut stack,
                &mut edge_stack,
                &mut on_stack,
            ) {
                eprintln!(
                    "The `join` implementation is not correct for type {}.
                    Either join(a, b) ⊑ a or join(a, b) ⊑ b is not satisfied.
                    Namely, there is a cycle in the subgraph of recorded join computations.
                    For more information see the documentation of JoinLatticeVerifier.",
                    std::any::type_name::<T>()
                );

                let block = cycle[0].1.block();

                eprintln!("The violation is in block {:?}", block);

                // Print the join sequence that led to the cycle
                for i in 0..cycle.len() {
                    assert_eq!(cycle[i].1.block(), block);
                    let other_block = weights[i].block();
                    eprintln!("Join #{}: {:?} {}", i, other_block, if ctxt.is_back_edge(other_block, block) {
                        " (backedge)"
                    } else {
                        ""
                    });
                }

                eprintln!("{:?} initial state:", block,);
                for line in cycle[0].1.debug_lines(ctxt) {
                    eprintln!("  {}", line);
                }
                for i in 1..cycle.len() + 1 {
                    let prev_state = &cycle[i - 1].1;
                    let prev_other_state = &weights[i - 1];
                    let next_state = &cycle[i % cycle.len()].1;
                    eprintln!(
                        "Joined with block {:?}, with the following diff vs {:?}",
                        prev_other_state.block(),
                        block
                    );
                    eprintln!("{}", prev_state.fmt_diff(prev_other_state, ctxt));

                    eprintln!(
                        "The result diff vs {:?} was:\n {}",
                        block,
                        prev_state.fmt_diff(next_state, ctxt)
                    );

                    // eprintln!("With resulting state:");
                    // for line in next_state.debug_lines(ctxt) {
                    //     eprintln!("  {}", line);
                    // }
                }
                // eprintln!("Node diffs:");
                // for i in 0..cycle.len() {
                //     let (_, curr) = &cycle[i];
                //     let (_, next) = &cycle[(i + 1) % cycle.len()];
                //     eprintln!("{}\n---\n", curr.fmt_diff(next, ctxt));
                // }

                // // Print the entire graph structure
                // eprintln!("\nComplete Graph Structure:");
                // eprintln!("Nodes:");
                // for node_idx in self.graph.node_indices() {
                //     eprintln!("Node {:?}", node_idx);
                //     for line in self.graph[node_idx].debug_lines(ctxt) {
                //         eprintln!("  {}", line);
                //     }
                //     eprintln!();
                // }
                // eprintln!("\nEdges:");
                // for edge in self.graph.edge_indices() {
                //     let (source, target) = self.graph.edge_endpoints(edge).unwrap();
                //     let weight = self.graph.edge_weight(edge).unwrap();
                //     eprintln!("{:?} -[{:?}]-> {:?}", source, weight, target);
                // }

                panic!("Join lattice must be acyclic.");
            }
        }
    }

    fn get_or_add_node(&mut self, value: T) -> petgraph::graph::NodeIndex {
        // Try to find existing node with this value
        for node_idx in self.graph.node_indices() {
            if self.graph[node_idx] == value {
                return node_idx;
            }
        }
        // If not found, add new node
        self.graph.add_node(value)
    }
}
