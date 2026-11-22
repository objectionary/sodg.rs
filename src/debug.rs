// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::fmt::{self, Debug, Display, Formatter};

use anyhow::{Context as _, Result};

use crate::{Kind, Persistence, Sodg};

impl<const N: usize> Display for Sodg<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        <&Self as Debug>::fmt(&self, f)
    }
}

impl<const N: usize> Debug for Sodg<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut lines = vec![];
        for (v, cell) in self.cells.iter() {
            if cell.branch == 0 {
                continue;
            }
            let mut attrs = cell
                .edges
                .iter()
                .map(|e| format!("\n\t{} ➞ c{}", e.0, e.1))
                .collect::<Vec<String>>();
            if cell.persistence != Persistence::Empty {
                attrs.push(format!("{}", cell.data));
            }
            if let Some(name) = &cell.lambda {
                attrs.push(format!("λ ⤍ {name}"));
            }
            let kind = match cell.kind {
                Kind::Void => String::new(),
                Kind::Formation => "F ".to_string(),
                Kind::Dispatch(a) => format!("D.{a} "),
                Kind::Application(a) => format!("A({a}) "),
            };
            lines.push(format!("c{v} -> {kind}⟦{}⟧", attrs.join(", ")));
        }
        for (b, members) in self.branches.iter() {
            if members.is_empty() {
                continue;
            }
            lines.push(format!(
                "b{b}: {{{}}}",
                members
                    .into_iter()
                    .map(|v| format!("c{v}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ));
        }
        f.write_str(lines.join("\n").as_str())
    }
}

impl<const N: usize> Sodg<N> {
    /// Print a single cell to a string, which can be used for
    /// logging and debugging.
    ///
    /// # Errors
    ///
    /// If the cell is absent, an error may be returned.
    pub fn c_print(&self, c: usize) -> Result<String> {
        let cell = &self
            .cells
            .get(c)
            .with_context(|| format!("Can't find c{c}"))?;
        let list: Vec<String> = cell
            .edges
            .iter()
            .map(|e| format!("{}", e.0.clone()))
            .collect();
        Ok(format!(
            "c{c}⟦{}{}⟧",
            if cell.persistence == Persistence::Empty {
                ""
            } else {
                "Δ, "
            },
            list.join(", ")
        ))
    }
}

#[test]
fn prints_itself() {
    let mut g: Sodg<16> = Sodg::empty(256);
    g.formation(0, &[]);
    g.formation(1, &[]);
    assert_ne!("", format!("{g:?}"));
}

#[test]
fn displays_itself() {
    let mut g: Sodg<16> = Sodg::empty(256);
    g.formation(0, &[]);
    g.formation(1, &[]);
    assert_ne!("", format!("{g}"));
}
