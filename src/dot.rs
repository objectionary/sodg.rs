// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use itertools::Itertools;

use crate::{Label, Persistence, Sodg};

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
    /// g.add(0);
    /// g.put(0, &Hex::from_str_bytes("hello"));
    /// g.add(1);
    /// g.bind(0, 1, Label::from_str("foo").unwrap());
    /// g.bind(0, 1, Label::from_str("bar").unwrap());
    /// let dot = g.to_dot();
    /// println!("{}", dot);
    /// ```
    ///
    /// The printout will look approximately like this:
    ///
    /// ```text
    /// digraph {
    ///   v0[shape=circle,label="ν0"];
    ///   v0 -> v1 [label="bar"];
    ///   v0 -> v1 [label="foo"];
    ///   v1[shape=circle,label="ν1"];
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
        for (v, vtx) in self
            .vertices
            .iter()
            .sorted_by_key(|(v, _)| <usize>::clone(v))
        {
            lines.push(format!(
                "  v{v}[shape=circle,label=\"ν{v}\"{}]; {}",
                if vtx.persistence == Persistence::Empty {
                    ""
                } else {
                    ",color=\"#f96900\""
                },
                if vtx.persistence == Persistence::Empty {
                    String::new()
                } else {
                    format!("/* {} */", vtx.data)
                },
            ));
            for e in vtx.edges.iter().sorted_by_key(|e| e.0) {
                lines.push(format!(
                    "  v{v} -> v{} [label=\"{}\"{}{}];",
                    e.1,
                    e.0,
                    match e.0 {
                        Label::Greek(g) => {
                            if *g == 'ρ' || *g == 'σ' {
                                ",color=gray,fontcolor=gray"
                            } else {
                                ""
                            }
                        }
                        _ => {
                            ""
                        }
                    },
                    match e.0 {
                        Label::Greek(g) => {
                            if *g == 'π' { ",style=dashed" } else { "" }
                        }
                        _ => {
                            ""
                        }
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
    g.add(0);
    g.put(0, &Hex::from_str_bytes("hello"));
    g.add(1);
    g.bind(0, 1, Label::Alpha(0));
    let dot = g.to_dot();
    assert!(dot.contains("shape=circle,label=\"ν0\""));
}
