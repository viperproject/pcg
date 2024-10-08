use petgraph::dot::{Config, Dot};
use petgraph::graphmap::DiGraphMap;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::Hash;

/// Generic type for Node, must implement required traits
type Node = &'static str;

#[derive(Clone, Debug)]
struct Edge<N> {
    from: N,
    to: N,
}

#[derive(Clone, Debug)]
pub struct Graph<N> {
    adjacency: HashMap<N, HashSet<N>>, // Node -> Set of adjacent nodes (LHS -> RHS)
}
impl<N> Graph<N>
where
    N: Eq + Hash + Clone + Copy + Ord + fmt::Debug,
{
    /// Converts the custom Graph into a petgraph DiGraphMap
    fn to_petgraph(&self) -> DiGraphMap<N, ()> {
        let mut graph = DiGraphMap::<N, ()>::new();
        for (from, tos) in &self.adjacency {
            for to in tos {
                graph.add_edge(from.clone(), to.clone(), ());
            }
        }
        graph
    }
}

impl<N> Graph<N>
where
    N: Eq + Hash + Clone + Copy + fmt::Debug,
{
    pub fn new() -> Self {
        Graph {
            adjacency: HashMap::new(),
        }
    }

    fn to_dot_petgraph(&self) -> String {
        let arena = bumpalo::Bump::new();
        let to_render: Graph<&str> = self.map(|e| {
            let node_name = format!("{:?}", e);
            let node_name = arena.alloc(node_name);
            node_name.as_str()
        });
        let dot = format!(
            "{:?}",
            Dot::with_config(&to_render.to_petgraph(), &[Config::EdgeNoLabel])
        );

        // Insert 'rankdir=LR;' after the first '{'
        let mut lines: Vec<&str> = dot.lines().collect();
        if let Some(index) = lines.iter().position(|&line| line.contains("{")) {
            lines.insert(index + 1, "    rankdir=LR;");
        }

        lines.join("\n")
    }

    pub fn map<F, T>(&self, f: F) -> Graph<T>
    where
        F: Fn(N) -> T,
        T: Eq + Hash + Clone + Copy + Ord + fmt::Debug,
    {
        let mut new_adjacency = HashMap::new();
        for (node, neighbors) in &self.adjacency {
            let new_node = f(*node);
            let new_neighbors = neighbors.iter().map(|n| f(*n)).collect();
            new_adjacency.insert(new_node, new_neighbors);
        }
        Graph {
            adjacency: new_adjacency,
        }
    }

    fn has_edges(&self) -> bool {
        for neighbors in self.adjacency.values() {
            if !neighbors.is_empty() {
                return true;
            }
        }
        false
    }

    pub fn add_edge(&mut self, from: N, to: N) {
        self.adjacency
            .entry(from.clone())
            .or_insert_with(HashSet::new)
            .insert(to.clone());
        // Ensure the 'to' node is in the adjacency map, even if it has no outgoing edges
        self.adjacency.entry(to).or_insert_with(HashSet::new);
    }

    /// Adds edges between consecutive nodes in the provided path.
    /// For example, given ["A", "B", "C"], it adds edges A -> B and B -> C.
    fn add_edges(&mut self, nodes: Vec<N>) {
        if nodes.len() < 2 {
            return; // Need at least two nodes to create an edge
        }

        for i in 0..nodes.len() - 1 {
            let from = nodes[i].clone();
            let to = nodes[i + 1].clone();
            self.add_edge(from, to);
        }
    }

    fn remove_edge(&mut self, from: &N, to: &N) {
        if let Some(neighbors) = self.adjacency.get_mut(from) {
            neighbors.remove(to);
            // Keep 'from' node in adjacency even if it has no more outgoing edges
        }
    }

    /// Checks if a node is a leaf (i.e., has no incoming edges)
    fn is_leaf(&self, node: &N) -> bool {
        !self
            .adjacency
            .values()
            .any(|neighbors| neighbors.contains(node))
    }

    fn is_disconnected(&self, node: &N) -> bool {
        self.is_leaf(node) && self.adjacency.get(node).map_or(true, HashSet::is_empty)
    }

    fn remove_node(&mut self, node: &N) {
        self.adjacency.remove(node);
        for neighbors in self.adjacency.values_mut() {
            neighbors.remove(node);
        }
    }

    /// Returns all nodes in the graph
    fn get_all_nodes(&self) -> HashSet<N> {
        let mut nodes = self.adjacency.keys().cloned().collect::<HashSet<_>>();
        for neighbors in self.adjacency.values() {
            nodes.extend(neighbors.clone());
        }
        nodes
    }

    /// Returns the leaf nodes (nodes with no incoming edges)
    fn get_leaf_nodes(&self) -> Vec<N> {
        let all_nodes = self.get_all_nodes();
        all_nodes
            .into_iter()
            .filter(|node| self.is_leaf(node))
            .collect()
    }

    /// Checks if there is an edge from `from` to `to`
    fn has_edge(&self, from: &N, to: &N) -> bool {
        if let Some(neighbors) = self.adjacency.get(from) {
            neighbors.contains(to)
        } else {
            false
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct HyperEdge<N> {
    lhs: BTreeSet<N>,
    rhs: BTreeSet<N>,
}

impl<N: Ord> HyperEdge<N> {
    fn new(lhs: BTreeSet<N>, rhs: BTreeSet<N>) -> Self {
        HyperEdge { lhs, rhs }
    }
    pub fn lhs(&self) -> &BTreeSet<N> {
        &self.lhs
    }
    pub fn rhs(&self) -> &BTreeSet<N> {
        &self.rhs
    }
}

#[derive(Clone, Debug)]
pub struct HyperGraph<N> {
    hyperedges: BTreeSet<HyperEdge<N>>,
}

impl<N: Ord> HyperGraph<N> {
    fn new() -> Self {
        HyperGraph {
            hyperedges: BTreeSet::new(),
        }
    }

    fn add_hyperedge(&mut self, hyperedge: HyperEdge<N>) {
        self.hyperedges.insert(hyperedge);
    }

    pub fn edges(&self) -> impl Iterator<Item = &HyperEdge<N>> {
        self.hyperedges.iter()
    }
}

impl<N> fmt::Display for Graph<N>
where
    N: Eq + Hash + Clone + fmt::Display + Copy + Ord + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (from, tos) in &self.adjacency {
            if tos.is_empty() {
                writeln!(f, "{} -> []", from)?;
            } else {
                let to_nodes: Vec<_> = tos.iter().collect();
                writeln!(f, "{} -> {:?}", from, to_nodes)?;
            }
        }
        Ok(())
    }
}

fn simple_triangle() -> (Graph<Node>, Graph<Node>) {
    // Create graphs G1 and G2
    let mut g1 = Graph::new();
    let mut g2 = Graph::new();

    // Build Graph 1
    // x1 -> a -> b -> x
    g1.add_edges(vec!["x1", "a", "x"]);
    // y1 -> c -> y
    g1.add_edges(vec!["y1", "y"]);

    // Build Graph 2
    // x1 -> c -> a -> x
    g2.add_edges(vec!["x1", "x"]);
    // y1 -> b -> y
    g2.add_edges(vec!["y1", "a", "y"]);

    (g1, g2)
}

fn triangle() -> (Graph<Node>, Graph<Node>) {
    // Create graphs G1 and G2
    let mut g1 = Graph::new();
    let mut g2 = Graph::new();

    // Build Graph 1
    // x1 -> a -> b -> x
    g1.add_edges(vec!["x1", "a", "b", "x"]);
    // y1 -> c -> y
    g1.add_edges(vec!["y1", "c", "y"]);

    // Build Graph 2
    // x1 -> c -> a -> x
    g2.add_edges(vec!["x1", "c", "a", "x"]);
    // y1 -> b -> y
    g2.add_edges(vec!["y1", "b", "y"]);

    (g1, g2)
}
fn acbd() -> (Graph<&'static str>, Graph<&'static str>) {
    // Create graphs G1 and G2
    let mut g1 = Graph::new();
    let mut g2 = Graph::new();

    // Build Graph 1
    // x1 -> a -> b -> x
    g1.add_edges(vec!["x1", "a", "b", "x"]);
    // y1 -> c -> d -> y
    g1.add_edges(vec!["y1", "c", "d", "y"]);

    // Build Graph 2
    // x1 -> c -> a -> x
    g2.add_edges(vec!["x1", "a", "c", "x"]);
    // y1 -> d -> b -> y
    g2.add_edges(vec!["y1", "b", "d", "y"]);

    (g1, g2)
}

fn cadb() -> (Graph<&'static str>, Graph<&'static str>) {
    // Create graphs G1 and G2
    let mut g1 = Graph::new();
    let mut g2 = Graph::new();

    // Build Graph 1
    // x1 -> a -> b -> x
    g1.add_edges(vec!["x1", "a", "b", "x"]);
    // y1 -> c -> d -> y
    g1.add_edges(vec!["y1", "c", "d", "y"]);

    // Build Graph 2
    // x1 -> c -> a -> x
    g2.add_edges(vec!["x1", "c", "a", "x"]);
    // y1 -> d -> b -> y
    g2.add_edges(vec!["y1", "d", "b", "y"]);

    (g1, g2)
}

// fn main() {
//     // Create graphs G1 and G2
//     let (mut g1, mut g2) = simple_triangle();
//     // Run the coupling algorithm
//     let g = coupling_algorithm(&mut g1, &mut g2);

//     println!("Resulting HyperGraph G:");
//     for (i, hyperedge) in g.hyperedges.iter().enumerate() {
//         println!(
//             "Hyperedge {}: {:?} -> {:?}",
//             i, hyperedge.lhs, hyperedge.rhs
//         );
//     }

//     // Optionally, generate DOT representations
//     let dot_g1 = g1.to_dot_petgraph();
//     let dot_g2 = g2.to_dot_petgraph();
//     println!("DOT Representation of G1:\n{}", dot_g1);
//     println!("DOT Representation of G2:\n{}", dot_g2);
// }

pub fn coupling_algorithm<N>(mut g1: Graph<N>, mut g2: Graph<N>) -> HyperGraph<N>
where
    N: Eq + Hash + Clone + Copy + Ord + fmt::Debug,
{
    let mut g = HyperGraph::new();

    'outer: while g1.has_edges() {
        // Get the current set of nodes in G1
        let n_stack: Vec<N> = g1.get_all_nodes().into_iter().collect();
        let mut n_queue = VecDeque::from(n_stack);

        while let Some(n) = n_queue.pop_front() {
            println!("Processing node: {:?}", n);

            if let Some((g1_prime, g2_prime, w)) = obtain(n.clone(), g1.clone(), g2.clone()) {
                g1 = g1_prime;
                g2 = g2_prime;
                g.add_hyperedge(w.clone());
                eprintln!("g1");
                g1.render_with_imgcat().unwrap();
                eprintln!("g2");
                g2.render_with_imgcat().unwrap();
                eprintln!("w: {:?}", w);
                println!("Added hyperedge to G. Breaking out of inner loop.");
                continue 'outer;
            }
        }
        panic!("No progress made in the inner loop. Exiting.");
    }

    g
}

fn init_hypergraph<N>(n: &N, mut g: Graph<N>) -> Option<(HyperEdge<N>, Graph<N>)>
where
    N: Eq + Hash + Clone + Copy + Ord + fmt::Debug,
{
    if g.is_leaf(n) {
        // Return success(emptyset -> {n}, G)
        let w = HyperEdge::new(BTreeSet::new(), BTreeSet::from([n.clone()]));
        return Some((w, g));
    } else {
        // Collect candidates to avoid borrowing issues
        let candidates: Vec<N> = g
            .adjacency
            .iter()
            .filter(|(n_prime, neighbors)| neighbors.contains(n) && g.is_leaf(n_prime))
            .map(|(n_prime, _)| n_prime.clone())
            .collect();

        if let Some(n_prime) = candidates.into_iter().next() {
            // Remove e and n' from G
            g.remove_edge(&n_prime, n);
            g.remove_node(&n_prime);

            let w = HyperEdge::new(
                [n_prime.clone()].iter().cloned().collect(),
                [n.clone()].iter().cloned().collect(),
            );
            return Some((w, g));
        } else {
            return None;
        }
    }
}

fn obtain<N>(n: N, g1: Graph<N>, g2: Graph<N>) -> Option<(Graph<N>, Graph<N>, HyperEdge<N>)>
where
    N: Eq + Hash + Clone + Copy + Ord + fmt::Debug,
{
    // If n is a leaf in G1 and n is a leaf in G2, return failure
    if g1.is_leaf(&n) && g2.is_leaf(&n) {
        return None;
    }

    // W1, G1 <- InitHyperGraph(n, G1)
    let (mut w1, mut g1) = init_hypergraph(&n, g1)?;
    // W2, G2 <- InitHyperGraph(n, G2)
    let (mut w2, mut g2) = init_hypergraph(&n, g2)?;

    // For each n in lhs(W2) \ lhs(W1)
    let lhs_w2_minus_w1: BTreeSet<_> = w2.lhs.difference(&w1.lhs).cloned().collect();
    for n in lhs_w2_minus_w1 {
        let (w1_prime, g1_prime) = consume(&n, w1.clone(), g1.clone())?;
        w1 = w1_prime;
        g1 = g1_prime;
    }

    // For each n in lhs(W1) \ lhs(W2)
    let lhs_w1_minus_w2: BTreeSet<_> = w1.lhs.difference(&w2.lhs).cloned().collect();
    for n in lhs_w1_minus_w2 {
        let (w2_prime, g2_prime) = consume(&n, w2.clone(), g2.clone())?;
        w2 = w2_prime;
        g2 = g2_prime;
    }

    // Let R := rhs(W1) ∩ rhs(W2)
    let mut r: BTreeSet<N> = w1.rhs.intersection(&w2.rhs).cloned().collect();

    // For each n in rhs(W1) \ rhs(W2)
    let rhs_w1_minus_w2: BTreeSet<_> = w1.rhs.difference(&w2.rhs).cloned().collect();
    for n in rhs_w1_minus_w2 {
        if g2.is_leaf(&n) {
            r.insert(n);
        }
    }

    // For each n in rhs(W2) \ rhs(W1)
    let rhs_w2_minus_w1: BTreeSet<_> = w2.rhs.difference(&w1.rhs).cloned().collect();
    for n in rhs_w2_minus_w1 {
        if g1.is_leaf(&n) {
            r.insert(n);
        }
    }

    // W := lhs(W1) ∪ lhs(W2) -> R
    let lhs_union: BTreeSet<_> = w1.lhs.union(&w2.lhs).cloned().collect();

    let w = HyperEdge::new(lhs_union, r);

    Some((g1, g2, w))
}

fn consume<N>(n: &N, mut w: HyperEdge<N>, mut g: Graph<N>) -> Option<(HyperEdge<N>, Graph<N>)>
where
    N: Eq + Hash + Clone + Copy + Ord + fmt::Debug,
{
    if !g.is_leaf(n) {
        return None; // Return failure
    }

    if let Some(neighbors) = g.adjacency.get(n) {
        if !neighbors.is_empty() {
            // There is an edge n -> n' in G
            let n_prime = neighbors.iter().next().unwrap().clone();
            g.remove_edge(n, &n_prime);
            g.remove_node(n);
            w.rhs.insert(n_prime.clone());
            return Some((w, g));
        }
    }

    // Remove n from G
    g.remove_node(n);
    Some((w, g))
}

use std::io::{Read, Write};
use std::process::{Command, Stdio};

impl<N> Graph<N>
where
    N: Eq + Hash + Clone + Copy + fmt::Debug,
{
    /// Renders the graph using `dot` and displays it using `imgcat` without using temporary files.
    /// Requires `dot` and `imgcat` to be installed and available in the system PATH.
    pub fn render_with_imgcat(&self) -> std::io::Result<()> {
        // Generate DOT representation
        let dot = self.to_dot_petgraph();

        // Spawn 'dot' command, with stdin piped and stdout piped
        let mut dot_process = Command::new("dot")
            .args(&["-Tpng"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;

        {
            // Write the DOT content to 'dot's stdin
            let stdin = dot_process
                .stdin
                .as_mut()
                .expect("Failed to open dot stdin");
            stdin.write_all(dot.as_bytes())?;
        }

        // Read the output from 'dot'
        let dot_output = dot_process.wait_with_output()?;

        if !dot_output.status.success() {
            eprintln!("Error: dot command failed");
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "dot command failed",
            ));
        }

        // Now, feed the output into 'imgcat'
        let mut imgcat_process = Command::new("imgcat")
            .stdin(Stdio::piped())
            .stdout(Stdio::inherit()) // Pass through imgcat's stdout to the terminal
            .spawn()?;

        {
            let stdin = imgcat_process
                .stdin
                .as_mut()
                .expect("Failed to open imgcat stdin");
            stdin.write_all(&dot_output.stdout)?;
        }

        let imgcat_status = imgcat_process.wait()?;

        if !imgcat_status.success() {
            eprintln!("Error: imgcat command failed");
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "imgcat command failed",
            ));
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coupling_acbd() {
        let (mut g1, mut g2) = acbd();

        let hypergraph = coupling_algorithm(&mut g1, &mut g2);

        let expected_hyperedges = vec![
            HyperEdge::new(
                ["a", "y1"].iter().cloned().collect(), // lhs
                ["b", "c"].iter().cloned().collect(),  // rhs
            ),
            HyperEdge::new(
                ["b", "c"].iter().cloned().collect(),
                ["x", "d"].iter().cloned().collect(),
            ),
            HyperEdge::new(
                ["d"].iter().cloned().collect(),
                ["y"].iter().cloned().collect(),
            ),
            HyperEdge::new(
                ["x1"].iter().cloned().collect(),
                ["a"].iter().cloned().collect(),
            ),
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();

        assert_eq!(hypergraph.hyperedges, expected_hyperedges);
    }

    #[test]
    fn test_coupling_cadb() {
        let (mut g1, mut g2) = cadb();

        let hypergraph = coupling_algorithm(&mut g1, &mut g2);

        let expected_hyperedges = vec![
            HyperEdge::new(
                ["x1", "y1"].iter().cloned().collect(), // lhs
                ["c"].iter().cloned().collect(),        // rhs
            ),
            HyperEdge::new(
                ["c"].iter().cloned().collect(),
                ["a", "d"].iter().cloned().collect(),
            ),
            HyperEdge::new(
                ["a", "d"].iter().cloned().collect(),
                ["b"].iter().cloned().collect(),
            ),
            HyperEdge::new(
                ["b"].iter().cloned().collect(),
                ["x", "y"].iter().cloned().collect(),
            ),
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();

        assert_eq!(hypergraph.hyperedges, expected_hyperedges);
    }
    #[test]
    fn test_coupling_simple_triangle() {
        let (mut g1, mut g2) = simple_triangle();

        let hypergraph = coupling_algorithm(&mut g1, &mut g2);

        let expected_hyperedges = vec![
            HyperEdge::new(
                ["a"].iter().cloned().collect(),      // lhs
                ["x", "y"].iter().cloned().collect(), // rhs
            ),
            HyperEdge::new(
                ["x1", "y1"].iter().cloned().collect(),
                ["a"].iter().cloned().collect(),
            ),
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();

        assert_eq!(hypergraph.hyperedges, expected_hyperedges);
    }

    #[test]
    fn test_coupling_triangle() {
        let (mut g1, mut g2) = triangle();

        let hypergraph = coupling_algorithm(&mut g1, &mut g2);

        let expected_hyperedges = vec![
            HyperEdge::new(
                ["x1", "y1"].iter().cloned().collect(), // lhs
                ["c"].iter().cloned().collect(),        // rhs
            ),
            HyperEdge::new(
                ["c"].iter().cloned().collect(),
                ["a"].iter().cloned().collect(),
            ),
            HyperEdge::new(
                ["a"].iter().cloned().collect(),
                ["b"].iter().cloned().collect(),
            ),
            HyperEdge::new(
                ["b"].iter().cloned().collect(),
                ["x", "y"].iter().cloned().collect(),
            ),
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();

        assert_eq!(hypergraph.hyperedges, expected_hyperedges);
    }
}
