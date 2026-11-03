// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::fmt::{self, Debug, Display, Formatter};

use anyhow::{Context as _, Result};
use itertools::Itertools as _;

use crate::{LabelId, Persistence, Sodg};

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
                .map(|(label, to)| format!("\n\t{} ➞ ν{to}", self.label_or_id(label)))
                .sorted()
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
                members
                    .into_iter()
                    .map(|v| format!("ν{v}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ));
        }
        f.write_str(lines.join("\n").as_str())
    }
}

impl<const N: usize> Sodg<N> {
    /// Render the label behind the identifier, or the identifier itself if
    /// this graph never interned it.
    ///
    /// Printing a graph is what explains a failure, including a failure of the
    /// assertion that a graph is well formed, so it must not add a panic of
    /// its own to the one being explained.
    fn label_or_id(&self, label: LabelId) -> String {
        self.labels
            .resolve_ref(label)
            .map_or_else(|| format!("#{label}"), ToString::to_string)
    }

    /// Print a single vertex to a string, which can be used for
    /// logging and debugging.
    ///
    /// # Errors
    ///
    /// If the vertex is absent, an error may be returned.
    pub fn v_print(&self, v: usize) -> Result<String> {
        let vtx = &self
            .vertices
            .get(v)
            .with_context(|| format!("Can't find ν{v}"))?;
        let list: Vec<String> = vtx
            .edges
            .iter()
            .map(|(label, _)| self.label_or_id(label))
            .sorted()
            .collect();
        Ok(format!(
            "ν{v}⟦{}{}⟧",
            if vtx.persistence == Persistence::Empty {
                ""
            } else {
                "Δ, "
            },
            list.join(", ")
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Label;

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

    fn star_of_five() -> Sodg<2> {
        let mut g: Sodg<2> = Sodg::empty(256);
        g.add(0);
        for i in 1..=5 {
            g.add(i);
            g.bind(0, i, Label::Alpha(i));
        }
        g
    }

    #[test]
    fn prints_edges_of_a_hashed_vertex_in_order() {
        let g = star_of_five();
        let text = format!("{g:?}");
        let at: Vec<usize> = (1..=5)
            .map(|i| text.find(&format!("α{i} ➞")).unwrap())
            .collect();
        assert!(at.windows(2).all(|w| w[0] < w[1]), "{text}");
    }

    #[test]
    fn prints_a_vertex_with_its_edges_in_order() {
        let g = star_of_five();
        let text = g.v_print(0).unwrap();
        let at: Vec<usize> = (1..=5)
            .map(|i| text.find(&format!("α{i}")).unwrap())
            .collect();
        assert!(at.windows(2).all(|w| w[0] < w[1]), "{text}");
    }

    #[test]
    fn prints_an_unknown_label_instead_of_panicking() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::Alpha(0));
        g.vertices.get_mut(0).unwrap().edges.insert(999, 1);
        assert!(format!("{g:?}").contains("#999"));
        assert!(g.v_print(0).unwrap().contains("#999"));
    }
}
