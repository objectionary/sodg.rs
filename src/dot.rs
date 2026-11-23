// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use itertools::Itertools;

use crate::{Label, Sodg};

impl<const N: usize> Sodg<N> {
    /// Print SODG as a DOT graph.
    ///
    /// For example, for this code:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Hex, Label};
    /// use sodg::Sodg;
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.formation(0, &[]);
    /// g.delta(0, &Hex::from_str_bytes("hello"));
    /// g.formation(1, &[]);
    /// g.put(0, Label::from_str("foo").unwrap(), 1);
    /// g.put(0, Label::from_str("bar").unwrap(), 1);
    /// let dot = g.to_dot();
    /// println!("{}", dot);
    /// ```
    ///
    /// The printout will look approximately like this:
    ///
    /// ```text
    /// digraph {
    ///   c0[shape=circle,label="c0"];
    ///   c0 -> c1 [label="bar"];
    ///   c0 -> c1 [label="foo"];
    ///   c1[shape=circle,label="c1"];
    /// }
    /// ```
    #[must_use]
    pub fn to_dot(&self) -> String {
        let mut lines: Vec<String> = vec![];
        lines.push(
            "/* Render it at https://dreampuf.github.io/GraphvizOnline/ */
digraph {
  node [fixedsize=true,width=1,fontname=\"Arial\"];
  edge [fontname=\"Arial\"];"
                .to_string(),
        );
        for (v, cell) in self
            .cells
            .iter()
            .filter(|(_, cell)| cell.made)
            .sorted_by_key(|(v, _)| *v)
        {
            lines.push(format!(
                "  c{v}[shape=circle,label=\"c{v}\"{}]; {}",
                if cell.data.is_some() {
                    ",color=\"#f96900\""
                } else {
                    ""
                },
                cell.data
                    .as_ref()
                    .map_or_else(String::new, |d| format!("/* {d} */")),
            ));
            for e in cell.edges.iter().sorted_by_key(|e| e.0) {
                lines.push(format!(
                    "  c{v} -> c{} [label=\"{}\"{}{}];",
                    e.1,
                    e.0.to_string()
                        .replace('\\', "\\\\")
                        .replace('"', "\\\"")
                        .replace('\n', "\\n")
                        .replace('\r', "\\r"),
                    match e.0 {
                        Label::Greek(g) if *g == 'ρ' || *g == 'σ' => {
                            ",color=gray,fontcolor=gray"
                        }
                        _ => "",
                    },
                    match e.0 {
                        Label::Greek(g) if *g == 'π' => ",style=dashed",
                        _ => "",
                    }
                ));
            }
        }
        lines.push("}\n".to_string());
        lines.join("\n")
    }
}

#[cfg(test)]
use crate::Hex;

#[test]
fn simple_graph_to_dot() {
    let mut g: Sodg<16> = Sodg::empty(256);
    g.formation(0, &[]);
    g.delta(0, &Hex::from_str_bytes("hello"));
    g.formation(1, &[]);
    g.put(0, Label::Alpha(0), 1);
    let dot = g.to_dot();
    assert!(dot.contains("shape=circle,label=\"c0\""));
}

#[test]
fn escapes_quotes_in_edge_labels() {
    use std::str::FromStr;
    let mut g: Sodg<16> = Sodg::empty(256);
    g.formation(0, &[]);
    g.formation(1, &[]);
    g.put(0, Label::from_str("a\"b").unwrap(), 1);
    let dot = g.to_dot();
    assert!(dot.contains("[label=\"a\\\"b\"]"), "{dot}");
}

#[test]
fn keeps_read_cells_in_dot() {
    let mut g: Sodg<16> = Sodg::empty(256);
    g.formation(1, &[]);
    g.formation(2, &[]);
    g.put(1, Label::Alpha(0), 2);
    g.delta(2, &Hex::from_str_bytes("hello"));
    assert!(g.data(2).is_some());
    assert_eq!(2, g.len());
    let dot = g.to_dot();
    assert!(dot.contains("label=\"c1\""));
    assert!(dot.contains("label=\"c2\""));
    assert!(!dot.contains("label=\"c0\""));
}
