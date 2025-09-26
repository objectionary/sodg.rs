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
        self.vertices
            .get(v)
            .with_context(|| format!("Can't find ν{v}"))?
            .edges
            .iter()
            .sorted_by_key(|edge| edge.label)
            .for_each(|edge| {
                let skip = seen.contains(&edge.to);
                let line = format!(
                    "  .{} ➞ ν{}{}",
                    edge.label,
                    edge.to,
                    if skip {
                        "…".to_owned()
                    } else {
                        String::new()
                    },
                );
                lines.push(line);
                if !skip {
                    seen.insert(edge.to);
                    self.inspect_v(edge.to, seen)
                        .unwrap()
                        .iter()
                        .for_each(|t| lines.push(format!("  {t}")));
                }
            });
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
}
