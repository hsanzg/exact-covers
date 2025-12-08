//! This program attempts to find a graceful labeling of an undirected graph.
// todo: define "graceful labeling", and mention where this XCC formulation
//       comes from.

use exact_covers::{DlSolver, Solver};
use std::collections::HashMap;
use std::fmt::Debug;
use std::io::BufRead;
use std::ops::ControlFlow;
use std::str::FromStr;

// todo: place `Graph` and all its related items after the main program.

type Name = String;
type Edge = (usize, usize, Name);

/// An undirected graph, represented as the list of its edges.
#[derive(Default)]
struct Graph {
    vertex_names: Vec<Name>,
    edges: Vec<Edge>,
}

impl Graph {
    /// Reads a graph in the [Trivial Graph Format][tgf].
    ///
    /// [tgf]: https://en.wikipedia.org/wiki/Trivial_Graph_Format
    pub fn read<R: BufRead>(reader: R) -> Self {
        type VertexId = u16;
        let mut lines = reader.lines().map(Result::unwrap);
        let mut vertex_ixs = HashMap::new();
        let mut vertex_labels = Vec::new();
        while let Some(line) = lines.next()
            && line != "#"
        {
            let (id, label) = line.split_once(' ').unwrap();
            let id = id.parse::<VertexId>().expect("invalid vertex id");
            vertex_ixs.insert(id, vertex_ixs.len());
            vertex_labels.push(label.into());
        }
        Self {
            vertex_names: vertex_labels,
            edges: lines
                .map(|l| {
                    let mut parts = l.splitn(3, ' ');
                    let mut next_endpoint = || {
                        parts
                            .next()
                            .expect("missing endpoint")
                            .parse()
                            .expect("invalid endpoint id")
                    };
                    let (u, v) = (next_endpoint(), next_endpoint());
                    let label = parts.next().unwrap_or_default().to_string();
                    (u, v, label)
                })
                .map(|(u, v, label)| (vertex_ixs[&u], vertex_ixs[&v], label))
                .collect(),
        }
    }

    pub fn num_vertices(&self) -> usize {
        self.vertex_names.len()
    }

    pub fn num_edges(&self) -> usize {
        self.edges.len()
    }
}

impl FromStr for Graph {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::read(s.as_bytes()))
    }
}

type VertexLabeling = Vec<usize>;

fn graceful(graph: &Graph, mut visit: impl FnMut(&VertexLabeling) -> ControlFlow<()>) {
    // todo: document that this formulation comes from exercise 7.2.2.3-69
    //       of TAOCP.
    #[derive(PartialEq, Eq, Clone, Copy, Debug)]
    enum Item {
        // Primary.
        EdgeLabel(usize),
        Edge(usize, usize),
        // Secondary.
        Vertex(usize),
        Holder(usize),
    }

    let (n, m) = (graph.num_vertices(), graph.num_edges());
    let edge_labels = (1..=m).map(Item::EdgeLabel);
    let edges = graph.edges.iter().map(|&(u, v, _)| Item::Edge(u, v));
    let vertices = (0..n).map(Item::Vertex);
    let holders = (0..=m).map(Item::Holder).collect::<Vec<_>>();

    let primary = edge_labels.chain(edges).collect::<Vec<_>>();
    let secondary = vertices.chain(holders).collect::<Vec<_>>();
    let mut solver = DlSolver::new(&primary, &secondary);

    for d in 1..=m {
        let label = Item::EdgeLabel(d);
        for (u, v, _) in &graph.edges {
            let edge = Item::Edge(*u, *v);
            let (i_u, i_v) = (Item::Vertex(*u), Item::Vertex(*v));
            for j in 0..=m - d {
                let k = j + d;
                solver.add_option(
                    // Assign label $d$ to edge $u-v$.
                    [label, edge],
                    [
                        // Assign labels $j$ and $k$, whose sum is $d$,
                        // to the endpoints $u$ and $v$, respectively.
                        (i_u, Some(j)),
                        (i_v, Some(k)),
                        (Item::Holder(j), Some(*u)),
                        (Item::Holder(k), Some(*v)),
                    ],
                );
            }
        }
    }
    // todo: break symmetry.

    let mut labeling = vec![0; n];
    solver.solve(|mut sol| {
        let mut option = Vec::new();
        while sol.next(&mut option) {
            if let &[(&Item::Vertex(u), Some(j)), (&Item::Vertex(v), Some(k))] = &option[2..4] {
                labeling[u] = j;
                labeling[v] = k;
            }
        }
        visit(&labeling)
    });
}

fn main() {
    let graph = Graph::read(std::io::stdin().lock());
    graceful(&graph, |labeling| {
        // todo: improve output formatting.
        println!("{labeling:?}");
        ControlFlow::Break(())
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn tgf() {
        let graph: Graph = "1 First node
2 Second node
3 Third node
#
1 2 First edge
1 3 Second edge"
            .parse()
            .unwrap();
        assert_eq!(graph.num_vertices(), 3);
        assert_eq!(graph.num_edges(), 2);
        assert_eq!(
            graph.vertex_names,
            &["First node", "Second node", "Third node"]
        );
        assert_eq!(
            graph.edges,
            &[
                (0, 1, "First edge".to_string()),
                (0, 2, "Second edge".to_string()),
            ]
        )
    }

    #[test]
    fn k3_2() {
        // The complete bipartite graph $K_{2,3}$ is graceful.
        let graph: Graph = "0 u_0
1 u_1
2 v_0
3 v_1
4 v_2
#
0 2
0 3
0 4
1 2
1 3
1 4"
        .parse()
        .unwrap();
        let (n, m) = (graph.num_vertices(), graph.num_edges());

        let mut found = false;
        graceful(&graph, |labeling| {
            found = true;

            // Check that the edge labels are distinct.
            let mut edge_labels = HashSet::new();
            for &(u, v, _) in &graph.edges {
                let (j, k) = (labeling[u], labeling[v]);
                let label = j.abs_diff(k);
                assert!(edge_labels.insert(label), "duplicate edge label");
            }

            // Check that the vertex labels are distinct and $\le m$.
            let uniq_vertex_labels = labeling
                .into_iter()
                .inspect(|&&l| assert!(l <= m))
                .collect::<HashSet<_>>();
            assert_eq!(uniq_vertex_labels.len(), n);
            ControlFlow::Break(())
        });
        assert!(found);
    }
}
