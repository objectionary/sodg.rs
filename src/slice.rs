// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::HashSet;

use anyhow::Result;
use log::trace;
use rustc_hash::FxHashMap;

use crate::{Label, LabelId, Sodg};

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
                for (a, to) in self.kids(v) {
                    if done.contains(to) {
                        continue;
                    }
                    if !p(v, *to, *a) {
                        continue;
                    }
                    done.insert(*to);
                    todo.insert(*to);
                }
            }
        }
        let mut ng = Self::empty(self.vertices.capacity());
        let mut remapped: FxHashMap<LabelId, LabelId> = FxHashMap::default();
        let kept: Vec<usize> = self
            .vertices
            .iter()
            .map(|(v1, _)| v1)
            .filter(|v1| done.contains(v1))
            .collect();
        for v1 in kept {
            ng.add(v1);
            let edges: Vec<(LabelId, usize)> = self
                .vertices
                .get(v1)
                .unwrap()
                .edges
                .iter()
                .filter(|&(_, v2)| done.contains(v2))
                .map(|(k, v2)| (k, *v2))
                .collect();
            for (k, v2) in edges {
                let id = *remapped.entry(k).or_insert_with(|| {
                    let a = self
                        .labels
                        .resolve(k)
                        .expect("Edge label was never interned");
                    ng.labels.intern(a)
                });
                ng.add(v2);
                ng.bind_interned(v1, v2, id);
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

    use tempfile::TempDir;

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
    fn keeps_every_label_of_the_slice_resolvable() {
        let mut g: Sodg<16> = Sodg::empty(256);
        for v in 0..=3 {
            g.add(v);
        }
        let foo = Label::from_str("foo").unwrap();
        let bar = Label::from_str("bar").unwrap();
        let baz = Label::from_str("baz").unwrap();
        g.bind(3, 0, baz);
        g.bind(0, 1, foo);
        g.bind(1, 2, bar);
        g.bind(2, 0, foo);
        let slice = g.slice(0).unwrap();
        assert_eq!(Some(1), slice.kid(0, foo));
        assert_eq!(Some(2), slice.kid(1, bar));
        assert_eq!(Some(0), slice.kid(2, foo));
        let names: Vec<String> = slice.kids(0).map(|(a, _)| a.to_string()).collect();
        assert_eq!(vec!["foo".to_string()], names);
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("slice.sodg");
        slice.save(file.as_path()).unwrap();
        Sodg::<16>::load(file.as_path())
            .expect("the slice carries an identifier its own interner can't resolve");
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
