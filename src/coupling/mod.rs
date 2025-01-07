use petgraph::dot::{Config, Dot};
use petgraph::graphmap::DiGraphMap;
use std::collections::{BTreeSet, HashSet, VecDeque};
use std::fmt;
use std::hash::Hash;

#[derive(Clone, Debug)]
pub struct Graph<N> {
    edges: HashSet<(N, N)>, // Set of edges (from, to)
}
impl<N> Graph<N>
where
    N: Eq + Hash + Clone + Copy + Ord + fmt::Debug,
{
    /// Converts the custom Graph into a petgraph DiGraphMap
    fn to_petgraph(&self) -> DiGraphMap<N, ()> {
        let mut graph = DiGraphMap::<N, ()>::new();
        for (from, to) in &self.edges {
            graph.add_edge(*from, *to, ());
        }
        graph
    }
}

impl<N> Graph<N>
where
    N: Eq + Hash + Clone + Copy + fmt::Display,
{
    pub fn new() -> Self {
        Graph {
            edges: HashSet::new(),
        }
    }

    pub fn edges(&self) -> impl Iterator<Item = &(N, N)> {
        self.edges.iter()
    }

    pub fn union(&self, other: &Self) -> Self {
        let mut new_edges = self.edges.clone();
        new_edges.extend(other.edges.iter().cloned());
        Graph { edges: new_edges }
    }

    pub fn transitive_reduction(&self) -> Self {
        let mut reduction = self.clone();

        // For each edge (u, v) in the graph
        for &(u, v) in &self.edges {
            // Skip if there's no need to process (u, v)
            if u == v {
                continue;
            }

            // Perform BFS to find all nodes reachable from 'v'
            let mut visited = HashSet::new();
            let mut queue = VecDeque::new();
            queue.push_back(v);
            visited.insert(v);

            while let Some(current) = queue.pop_front() {
                // If there's a direct edge from 'u' to 'current', and 'current' is not 'v'
                if current != v && reduction.has_edge(&u, &current) {
                    // Remove the redundant edge (u, current)
                    reduction.remove_edge(&u, &current);
                }

                for &(from, to) in &self.edges {
                    if from == current && !visited.contains(&to) {
                        visited.insert(to);
                        queue.push_back(to);
                    }
                }
            }
        }

        reduction
    }

    fn to_dot_petgraph(&self) -> String
    {
        let arena = bumpalo::Bump::new();
        let to_render: Graph<&str> = self.map(|e| {
            let node_name = format!("{}", e);
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
        let new_edges = self
            .edges
            .iter()
            .map(|(from, to)| (f(*from), f(*to)))
            .collect();
        Graph { edges: new_edges }
    }

    pub fn add_edge(&mut self, from: N, to: N) {
        if from == to {
            // TODO: Should we handle these here?
            eprintln!("self-loop edge");
            return;
        }
        self.edges.insert((from, to));
    }

    fn remove_edge(&mut self, from: &N, to: &N) {
        self.edges.remove(&(*from, *to));
    }

    /// Checks if a node is a leaf (i.e., has no outgoing edges)
    fn is_leaf(&self, node: &N) -> bool {
        !self.edges.iter().any(|(from, _)| from == node)
    }

    /// Returns all nodes in the graph
    fn get_all_nodes(&self) -> HashSet<N> {
        let mut nodes = HashSet::new();
        for (from, to) in &self.edges {
            nodes.insert(*from);
            nodes.insert(*to);
        }
        nodes
    }

    /// Returns the leaf nodes (nodes with no incoming edges)
    pub fn leaf_nodes(&self) -> Vec<N> {
        let all_nodes = self.get_all_nodes();
        all_nodes
            .into_iter()
            .filter(|node| self.is_leaf(node))
            .collect()
    }

    /// Checks if there is an edge from `from` to `to`
    fn has_edge(&self, from: &N, to: &N) -> bool {
        self.edges.contains(&(*from, *to))
    }

    pub fn nodes_pointing_to(&self, node: N) -> HashSet<N> {
        self.edges
            .iter()
            .filter_map(|(from, to)| if to == &node { Some(*from) } else { None })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct HyperEdge<N> {
    lhs: BTreeSet<N>,
    rhs: BTreeSet<N>,
}

impl<N: Ord> HyperEdge<N> {
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
    pub fn edges(&self) -> impl Iterator<Item = &HyperEdge<N>> {
        self.hyperedges.iter()
    }
}

impl<N> fmt::Display for Graph<N>
where
    N: Eq + Hash + Clone + fmt::Display + Copy + Ord + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (from, to) in &self.edges {
            writeln!(f, "{} -> {}", from, to)?;
        }
        Ok(())
    }
}

use crate::visualization::dot_graph::DotGraph;

impl<N> Graph<N>
where
    N: Eq + Hash + Clone + Copy + fmt::Display,
{
    /// Renders the graph using `dot` and displays it using `imgcat`.
    /// Requires `dot` and `imgcat` to be installed and available in the system PATH.
    /// If either is not installed, this function effectively does nothing.
    pub fn render_with_imgcat(&self) {
        fn go<N: Eq + Hash + Clone + Copy + fmt::Display>(
            graph: &Graph<N>,
        ) -> Result<(), std::io::Error> {
            let dot = graph.to_dot_petgraph();
            DotGraph::render_with_imgcat(&dot)
        }

        // This function is just for debugging, so we don't care if it fails
        go(self).unwrap_or_else(|e| {
            eprintln!("Error rendering graph: {}", e);
        });
    }
}
