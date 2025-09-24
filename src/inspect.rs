// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
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
    pub fn inspect(&self, v: usize) -> Result<String> {
        let mut seen = HashSet::new();
        Ok(format!(
            "ν{}\n{}",
            v,
            self.inspect_v(v, &mut seen)?.join("\n"),
        ))
    }

    fn inspect_v(&self, v: usize, seen: &mut HashSet<usize>) -> Result<Vec<String>> {
        seen.insert(v);
        let mut lines = vec![];
        let edges = {
            let vertex = self
                .vertices
                .get(v)
                .with_context(|| format!("Can't find ν{v}"))?;
            vertex
                .edges
                .iter()
                .sorted()
                .map(|(label, target)| (*label, *target))
                .collect::<Vec<_>>()
        };
        for (label, target) in edges {
            let skip = seen.contains(&target);
            let suffix = if skip { "…" } else { "" };
            lines.push(format!("  .{label} ➞ ν{target}{suffix}"));
            if skip {
                continue;
            }
            let inspected = self.inspect_v(target, seen)?;
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
        g.add(0);
        g.put(0, &Hex::from_str_bytes("hello"));
        g.add(1);
        let txt = g.inspect(0).unwrap();
        g.bind(0, 1, Label::Alpha(0));
        assert_ne!(String::new(), txt);
    }

    #[test]
    fn inspect_errors_if_child_vertex_missing() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::Alpha(0));
        g.vertices.remove(1);
        let result = g.inspect(0);
        assert!(result.is_err());
    }
}
