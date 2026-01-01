// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::HashSet;

use anyhow::Result;
use log::trace;

use crate::{Label, Sodg};

impl<const N: usize> Sodg<N> {
    /// Take a slice of the graph, keeping only the vertex specified
    /// by the locator and its kids, recursively found in the entire graph.
    ///
    /// # Errors
    ///
    /// If impossible to slice, an error will be returned.
    #[allow(clippy::use_self)]
    pub fn slice(&self, v: usize) -> Result<Self> {
        let g: Sodg<N> = self.slice_some(v, |_, _, _| true)?;
        trace!(
            "#slice: taken {} vertices out of {} at ν{v}",
            g.len(),
            self.len(),
        );
        Ok(g)
    }

    /// Take a slice of the graph, keeping only the vertex specified
    /// by the locator and its kids, recursively found in the entire graph,
    /// but only if the provided predicate agrees with the selection of
    /// the kids.
    ///
    /// # Errors
    ///
    /// There could be errors too.
    ///
    /// # Panics
    ///
    /// If impossible to slice, an error will be returned.
    pub fn slice_some(&self, v: usize, p: impl Fn(usize, usize, Label) -> bool) -> Result<Self> {
        let mut todo = HashSet::new();
        let mut done = HashSet::new();
        todo.insert(v);
        loop {
            if todo.is_empty() {
                break;
            }
            let before: Vec<usize> = todo.drain().collect();
            for v in before {
                done.insert(v);
                for e in &self.vertices.get(v).unwrap().edges {
                    if done.contains(e.1) {
                        continue;
                    }
                    if !p(v, *e.1, *e.0) {
                        continue;
                    }
                    done.insert(*e.1);
                    todo.insert(*e.1);
                }
            }
        }
        let mut ng = Self::empty(self.vertices.capacity());
        for (v1, vtx) in self.vertices.iter().filter(|(v, _)| done.contains(v)) {
            if done.contains(&v1) {
                ng.add(v1);
            }
            for (k, v2) in &vtx.edges {
                if done.contains(v2) {
                    ng.add(*v2);
                    ng.bind(v1, *v2, *k);
                }
            }
        }
        trace!(
            "#slice_some: taken {} vertices out of {} at ν{v}",
            ng.len(),
            self.len(),
        );
        Ok(ng)
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use super::*;

    #[test]
    fn makes_a_slice() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap());
        g.add(2);
        g.bind(0, 2, Label::from_str("bar").unwrap());
        assert_eq!(1, g.slice(1).unwrap().len());
        assert_eq!(1, g.slice(2).unwrap().len());
    }

    #[test]
    fn makes_a_partial_slice() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap());
        g.add(2);
        g.bind(1, 2, Label::from_str("bar").unwrap());
        let slice = g.slice_some(1, |_v, _to, _a| false).unwrap();
        assert_eq!(1, slice.len());
    }

    #[test]
    fn skips_some_vertices() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap());
        g.add(2);
        g.bind(0, 2, Label::from_str("+bar").unwrap());
        let slice = g
            .slice_some(0, |_, _, a| !a.to_string().starts_with('+'))
            .unwrap();
        assert_eq!(2, slice.len());
        assert_eq!(1, slice.kids(0).count());
    }
}
