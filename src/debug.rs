// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::fmt::{self, Debug, Display, Formatter};

use anyhow::{Context as _, Result};

use crate::{Persistence, Sodg};

impl<const N: usize> Display for Sodg<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        <&Self as Debug>::fmt(&self, f)
    }
}

impl<const N: usize> Debug for Sodg<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut lines = vec![];
        for (v, vtx) in self.vertices.iter() {
            if vtx.branch == 0 {
                continue;
            }
            let mut attrs = vtx
                .edges
                .iter()
                .map(|edge| {
                    let label = self.edge_label_text(edge);
                    format!("\n\t{label} ➞ ν{}", edge.to)
                })
                .collect::<Vec<String>>();
            if vtx.persistence != Persistence::Empty {
                attrs.push(format!("{}", vtx.data));
            }
            lines.push(format!("ν{v} -> ⟦{}⟧", attrs.join(", ")));
        }
        for (b, members) in self.branches.iter() {
            if members.is_empty() {
                continue;
            }
            lines.push(format!(
                "b{b}: {{{}}}",
                members.into_iter().map(|v| format!("ν{v}")).collect::<Vec<String>>().join(", ")
            ));
        }
        f.write_str(lines.join("\n").as_str())
    }
}

impl<const N: usize> Sodg<N> {
    /// Print a single vertex to a string, which can be used for
    /// logging and debugging.
    ///
    /// # Errors
    ///
    /// If the vertex is absent, an error may be returned.
    pub fn v_print(&self, v: usize) -> Result<String> {
        let vtx = &self.vertices.get(v).with_context(|| format!("Can't find ν{v}"))?;
        let list: Vec<String> =
            vtx.edges.iter().map(|edge| self.edge_label_text(edge).into_owned()).collect();
        Ok(format!(
            "ν{v}⟦{}{}⟧",
            if vtx.persistence == Persistence::Empty { "" } else { "Δ, " },
            list.join(", ")
        ))
    }
}

#[test]
fn prints_itself() {
    let mut g: Sodg<16> = Sodg::empty(256);
    g.add(0);
    g.add(1);
    assert_ne!("", format!("{g:?}"));
}

#[test]
fn displays_itself() {
    let mut g: Sodg<16> = Sodg::empty(256);
    g.add(0);
    g.add(1);
    assert_ne!("", format!("{g}"));
}
