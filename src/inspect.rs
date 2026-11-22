// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::HashSet;

use anyhow::{Context as _, Result};
use itertools::Itertools;

use crate::Sodg;

impl<const N: usize> Sodg<N> {
    /// Find an object by the provided locator and print its tree
    /// of sub-objects and edges.
    ///
    /// The function is mostly used for testing.
    ///
    /// # Errors
    ///
    /// If it's impossible to inspect, an error will be returned.
    pub fn inspect(&self, c: usize) -> Result<String> {
        let mut seen = HashSet::new();
        Ok(format!(
            "c{}\n{}",
            c,
            self.inspect_c(c, &mut seen)?.join("\n"),
        ))
    }

    fn inspect_c(&self, v: usize, seen: &mut HashSet<usize>) -> Result<Vec<String>> {
        seen.insert(v);
        let mut lines = vec![];
        let edges = {
            let cell = self
                .cells
                .get(v)
                .with_context(|| format!("Can't find c{v}"))?;
            cell.edges
                .iter()
                .sorted()
                .map(|(label, target)| (*label, *target))
                .collect::<Vec<_>>()
        };
        for (label, target) in edges {
            let skip = seen.contains(&target);
            let suffix = if skip { "…" } else { "" };
            lines.push(format!("  .{label} ➞ c{target}{suffix}"));
            if skip {
                continue;
            }
            let inspected = self.inspect_c(target, seen)?;
            for nested in inspected {
                lines.push(format!("  {nested}"));
            }
        }
        Ok(lines)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Hex;
    use crate::Label;

    #[test]
    fn inspects_simple_object() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.delta(0, &Hex::from_str_bytes("hello"));
        g.formation(1, &[]);
        let txt = g.inspect(0).unwrap();
        g.put(0, Label::Alpha(0), 1);
        assert_ne!(String::new(), txt);
    }

    #[test]
    fn inspect_errors_if_child_cell_missing() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::Alpha(0), 1);
        g.cells.remove(1);
        let result = g.inspect(0);
        assert!(result.is_err());
    }
}
