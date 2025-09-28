// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::HashSet;

use anyhow::{Context as _, Result};

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
        let vertex = self
            .vertices
            .get(v)
            .with_context(|| format!("Can't find ν{v}"))?;
        let mut edges = vertex
            .edges
            .iter()
            .map(|edge| (self.edge_label_text(edge).into_owned(), edge.to))
            .collect::<Vec<_>>();
        edges.sort_by(|left, right| left.0.cmp(&right.0));
        for (label, destination) in edges {
            let skip = seen.contains(&destination);
            let mut line = format!("  .{label} ➞ ν{destination}");
            if skip {
                line.push('…');
            }
            lines.push(line);
            if skip {
                continue;
            }
            seen.insert(destination);
            for text in self.inspect_v(destination, seen)? {
                lines.push(format!("  {text}"));
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
        g.bind(0, 1, Label::Alpha(0)).unwrap();
        assert_ne!(String::new(), txt);
    }
}
