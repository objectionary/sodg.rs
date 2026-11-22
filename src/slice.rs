// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::HashSet;

use anyhow::Result;
use log::trace;

use crate::{Label, Sodg};

impl<const N: usize> Sodg<N> {
    /// Take a slice of the graph, keeping only the cell specified
    /// by the locator and its kids, recursively found in the entire graph.
    ///
    /// # Errors
    ///
    /// If impossible to slice, an error will be returned.
    #[allow(clippy::use_self)]
    pub fn slice(&self, c: usize) -> Result<Self> {
        let g: Sodg<N> = self.slice_some(c, |_, _, _| true)?;
        trace!(
            "#slice: taken {} cells out of {} at c{c}",
            g.len(),
            self.len(),
        );
        Ok(g)
    }

    /// Take a slice of the graph, keeping only the cell specified
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
    pub fn slice_some(&self, c: usize, p: impl Fn(usize, usize, Label) -> bool) -> Result<Self> {
        let mut todo = HashSet::new();
        let mut done = HashSet::new();
        todo.insert(c);
        loop {
            if todo.is_empty() {
                break;
            }
            let before: Vec<usize> = todo.drain().collect();
            for c in before {
                done.insert(c);
                for e in &self.cells.get(c).unwrap().edges {
                    if done.contains(e.1) {
                        continue;
                    }
                    if !p(c, *e.1, *e.0) {
                        continue;
                    }
                    done.insert(*e.1);
                    todo.insert(*e.1);
                }
            }
        }
        let mut ng = Self::empty(self.cells.capacity());
        for (v1, cell) in self.cells.iter().filter(|(c, _)| done.contains(c)) {
            ng.make(v1);
            let copy = ng.cells.get_mut(v1).unwrap();
            copy.kind = cell.kind;
            copy.attrs.clone_from(&cell.attrs);
            copy.lambda.clone_from(&cell.lambda);
            for (k, v2) in &cell.edges {
                if done.contains(v2) {
                    ng.make(*v2);
                    ng.link(v1, *v2, *k);
                }
            }
        }
        trace!(
            "#slice_some: taken {} cells out of {} at c{c}",
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
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("foo").unwrap(), 1);
        g.formation(2, &[]);
        g.put(0, Label::from_str("bar").unwrap(), 2);
        assert_eq!(1, g.slice(1).unwrap().len());
        assert_eq!(1, g.slice(2).unwrap().len());
    }

    #[test]
    fn keeps_kinds_in_slice() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let x = Label::from_str("x").unwrap();
        g.formation(0, &[x]);
        g.lambda(0, "L_foo");
        g.formation(1, &[]);
        g.put(0, x, 1);
        g.dispatch(2, 0, x);
        let slice = g.slice(2).unwrap();
        assert_eq!(3, slice.len());
        assert_eq!(crate::Kind::Dispatch(x), slice.kind(2));
        assert_eq!(&[x], slice.attrs(0));
        assert_eq!(Some("L_foo"), slice.atom(0));
    }

    #[test]
    fn makes_a_partial_slice() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("foo").unwrap(), 1);
        g.formation(2, &[]);
        g.put(1, Label::from_str("bar").unwrap(), 2);
        let slice = g.slice_some(1, |_v, _to, _a| false).unwrap();
        assert_eq!(1, slice.len());
    }

    #[test]
    fn skips_some_cells() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("foo").unwrap(), 1);
        g.formation(2, &[]);
        g.put(0, Label::from_str("+bar").unwrap(), 2);
        let slice = g
            .slice_some(0, |_, _, a| !a.to_string().starts_with('+'))
            .unwrap();
        assert_eq!(2, slice.len());
        assert_eq!(1, slice.kids(0).count());
    }
}
