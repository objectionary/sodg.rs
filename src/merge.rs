// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::{HashMap, HashSet};

use anyhow::{Context, Result, bail};
use log::debug;

use crate::{Kind, Label, Sodg};

impl<const N: usize> Sodg<N> {
    /// Merge another graph into the current one.
    ///
    /// It is expected that both graphs are trees! If they are not, the result is unpredictable.
    ///
    /// The `right` cell is mapped to the `left` cell. The decisions about
    /// their kids are made recursively.
    ///
    /// The `left` cell is expected
    /// to be the root of the current graph, while the `right` cell is the root
    /// of the graph being merged into the current one.
    ///
    /// # Errors
    ///
    /// If it's impossible to merge, an error will be returned.
    pub fn merge(&mut self, g: &Self, left: usize, right: usize) -> Result<()> {
        if self.cells.get(left).is_none_or(|c| !c.made) {
            bail!("Can't find c{left} in the destination graph");
        }
        let mut mapped = HashMap::new();
        let before = self.len();
        self.merge_rec(g, left, right, &mut mapped)?;
        let merged = mapped.len();
        let scope = g.len();
        if merged != scope {
            let must = g.keys();
            let seen = mapped.keys().copied().collect::<Vec<usize>>();
            let missed: HashSet<usize> =
                &HashSet::from_iter(must.clone()) - &HashSet::from_iter(seen.clone());
            let mut ordered: Vec<usize> = missed.into_iter().collect();
            ordered.sort_unstable();
            bail!(
                "Just {merged} cells merged, out of {scope} (must={}, seen={}); maybe the right graph was not a tree? {} missed: {}",
                must.len(),
                seen.len(),
                ordered.len(),
                ordered
                    .iter()
                    .map(|v| format!("c{v}"))
                    .collect::<Vec<String>>()
                    .join(", "),
            );
        }
        debug!(
            "Merged all {merged} cells into SODG of {}, making it have {} after the merge",
            before,
            self.len(),
        );
        Ok(())
    }

    /// Merge two trees recursively, ignoring nodes already in `mapped`.
    ///
    /// `right` cell (from `g`) is mapped onto `left` cell (in `self`).
    /// Children decisions are made recursively.
    ///
    /// `mapped`: key is a cell from the right graph, value is the mapped cell in the left graph.
    ///
    /// # Errors
    /// Returns an error if merge is impossible (e.g., missing cell).
    #[allow(clippy::option_if_let_else)]
    fn merge_rec(
        &mut self,
        g: &Self,
        left: usize,
        right: usize,
        mapped: &mut HashMap<usize, usize>,
    ) -> Result<()> {
        // If already mapped, nothing to do
        if mapped.contains_key(&right) {
            return Ok(());
        }

        // Record mapping early to avoid cycles re-entering here
        mapped.insert(right, left);

        // Access cell safely
        let v = g
            .cells
            .get(right)
            .with_context(|| format!("Can't find c{right}"))?;

        // Merge payload if present
        if let Some(d) = &v.data {
            // delta: merges data from right into left
            self.delta(left, d);
        }

        // Merge the kind, the attributes, and the λ-asset, if present
        if v.kind != Kind::Void {
            let cell = self.cells.get_mut(left).unwrap();
            cell.kind = v.kind;
            cell.attrs.clone_from(&v.attrs);
        }
        if v.lambda.is_some() {
            self.cells
                .get_mut(left)
                .unwrap()
                .lambda
                .clone_from(&v.lambda);
        }

        // First pass: ensure all children exist and recurse
        for (a, to) in g.kids(right) {
            // `self.kid` returns Option<usize> for child by attribute `a`
            let matched = if let Some(t) = self.kid(left, *a) {
                t
            } else if let Some(&t) = mapped.get(to) {
                // Child already mapped elsewhere; link current edge to that node
                self.link(left, t, *a);
                t
            } else {
                // Create new node, bind, and continue
                let id = self.next_id();
                self.make(id);
                self.link(left, id, *a);
                id
            };

            // Recurse into the matched/created child
            self.merge_rec(g, matched, *to, mapped)?;
        }

        // Second pass: if multiple paths led to different nodes, join them
        for (a, to) in g.kids(right) {
            if let Some(first) = self.kid(left, *a)
                && let Some(&second) = mapped.get(to)
                && first != second
            {
                self.join(first, second);
            }
        }

        Ok(())
    }

    fn join(&mut self, left: usize, right: usize) {
        for v in self.keys() {
            let mut nv = self.cells.get(v).unwrap().clone();
            for e in &self.cells.get_mut(v).unwrap().edges {
                if *e.1 == right {
                    nv.edges.insert(*e.0, left);
                }
            }
            self.cells.insert(v, nv);
        }
        let kids = self
            .kids(right)
            .map(|(a, v)| (*a, *v))
            .collect::<Vec<(Label, usize)>>();
        for e in kids {
            assert!(
                self.kid(left, e.0).is_none(),
                "Can't merge c{right} into c{left}, due to conflict in '{}'",
                e.0,
            );
            self.link(left, e.1, e.0);
        }
        self.cells.remove(right);
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use super::*;

    #[test]
    fn rejects_missing_left_with_empty_right() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let mut extra: Sodg<16> = Sodg::empty(256);
        extra.formation(0, &[]);
        assert!(g.merge(&extra, 0, 0).is_err());
    }

    #[test]
    fn rejects_missing_left_with_data_in_right() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let mut extra: Sodg<16> = Sodg::empty(256);
        extra.formation(0, &[]);
        extra.delta(0, &Hex::from(42));
        assert!(g.merge(&extra, 0, 0).is_err());
    }

    #[test]
    fn merges_two_graphs() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("foo").unwrap(), 1);
        let mut extra = Sodg::empty(256);
        extra.formation(0, &[]);
        extra.formation(1, &[]);
        extra.put(0, Label::from_str("bar").unwrap(), 1);
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(3, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
        assert_eq!(2, g.kid(0, Label::from_str("bar").unwrap()).unwrap());
    }

    #[test]
    fn merges_two_non_trees() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        let mut extra = Sodg::empty(256);
        extra.formation(0, &[]);
        extra.formation(42, &[]);
        extra.formation(2, &[]);
        extra.formation(13, &[]);
        let r = g.merge(&extra, 0, 0);
        assert!(r.is_err());
        let msg = r.err().unwrap().to_string();
        assert!(msg.contains("c2, c13, c42"), "{}", msg);
    }

    #[test]
    fn reports_missing_cell() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        let mut extra = Sodg::empty(2);
        let missing = 1;
        extra.cells.remove(missing);
        let error = g.merge(&extra, 0, missing).unwrap_err();
        let message = error.to_string();
        let expected = format!("Can't find c{missing}");
        assert!(message.contains(&expected), "{message}");
    }

    #[test]
    fn merges_a_loop() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("a").unwrap(), 1);
        g.formation(2, &[]);
        g.put(1, Label::from_str("b").unwrap(), 2);
        let mut extra = Sodg::empty(256);
        extra.formation(0, &[]);
        extra.formation(4, &[]);
        extra.put(0, Label::from_str("c").unwrap(), 4);
        extra.formation(3, &[]);
        extra.put(0, Label::from_str("a").unwrap(), 3);
        extra.put(4, Label::from_str("d").unwrap(), 3);
        extra.formation(5, &[]);
        extra.put(3, Label::from_str("e").unwrap(), 5);
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(5, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("a").unwrap()).unwrap());
        assert_eq!(2, g.kid(1, Label::from_str("b").unwrap()).unwrap());
        // assert_eq!(3, g.kid(0, "c").unwrap());
        // assert_eq!(1, g.kid(3, "d").unwrap());
        // assert_eq!(5, g.kid(1, "e").unwrap());
    }

    #[test]
    fn avoids_simple_duplicates() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(5, &[]);
        g.put(0, Label::from_str("foo").unwrap(), 5);
        let mut extra = Sodg::empty(256);
        extra.formation(0, &[]);
        extra.formation(1, &[]);
        extra.put(0, Label::from_str("foo").unwrap(), 1);
        extra.formation(2, &[]);
        extra.put(1, Label::from_str("bar").unwrap(), 2);
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(3, g.len());
        assert_eq!(5, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
        assert_eq!(1, g.kid(5, Label::from_str("bar").unwrap()).unwrap());
    }

    #[test]
    fn keeps_existing_cells_intact() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("foo").unwrap(), 1);
        g.formation(2, &[]);
        g.put(1, Label::from_str("bar").unwrap(), 2);
        g.formation(3, &[]);
        g.put(2, Label::from_str("zzz").unwrap(), 3);
        let mut extra = Sodg::empty(256);
        extra.formation(0, &[]);
        extra.formation(5, &[]);
        extra.put(0, Label::from_str("foo").unwrap(), 5);
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(4, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
        assert_eq!(2, g.kid(1, Label::from_str("bar").unwrap()).unwrap());
        assert_eq!(3, g.kid(2, Label::from_str("zzz").unwrap()).unwrap());
    }

    #[test]
    fn merges_singletons() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(13, &[]);
        let mut extra = Sodg::empty(256);
        extra.formation(13, &[]);
        g.merge(&extra, 13, 13).unwrap();
        assert_eq!(1, g.len());
    }

    #[test]
    fn merges_simple_loop() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.put(1, Label::from_str("foo").unwrap(), 2);
        g.put(2, Label::from_str("bar").unwrap(), 1);
        let extra = g.clone();
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(extra.len(), g.len());
    }

    #[test]
    fn merges_large_loop() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.formation(3, &[]);
        g.formation(4, &[]);
        g.put(1, Label::from_str("a").unwrap(), 2);
        g.put(2, Label::from_str("b").unwrap(), 3);
        g.put(3, Label::from_str("c").unwrap(), 4);
        g.put(4, Label::from_str("d").unwrap(), 1);
        let extra = g.clone();
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(extra.len(), g.len());
    }

    #[cfg(test)]
    use crate::Hex;

    #[test]
    fn merges_data() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        let mut extra = Sodg::empty(256);
        extra.formation(1, &[]);
        extra.delta(1, &Hex::from(42_i64));
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(42, g.data(1).unwrap().to_i64().unwrap());
    }

    #[test]
    fn understands_same_name_kids() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("a").unwrap(), 1);
        g.formation(2, &[]);
        g.put(1, Label::from_str("x").unwrap(), 2);
        let mut extra = Sodg::empty(256);
        extra.formation(0, &[]);
        extra.formation(1, &[]);
        extra.put(0, Label::from_str("b").unwrap(), 1);
        extra.formation(2, &[]);
        extra.put(1, Label::from_str("x").unwrap(), 2);
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(5, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("a").unwrap()).unwrap());
        assert_eq!(2, g.kid(1, Label::from_str("x").unwrap()).unwrap());
    }

    #[test]
    fn merges_into_empty_graph() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        let mut extra = Sodg::empty(256);
        extra.formation(1, &[]);
        extra.formation(2, &[]);
        extra.formation(3, &[]);
        extra.put(1, Label::from_str("a").unwrap(), 2);
        extra.put(2, Label::from_str("b").unwrap(), 3);
        extra.put(3, Label::from_str("c").unwrap(), 1);
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(3, g.len());
        assert_eq!(0, g.kid(1, Label::from_str("a").unwrap()).unwrap());
    }

    #[test]
    fn mixed_injection() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(4, &[]);
        let mut extra = Sodg::empty(256);
        extra.formation(4, &[]);
        extra.delta(4, &Hex::from(4));
        extra.formation(5, &[]);
        extra.delta(5, &Hex::from(5));
        extra.put(4, Label::from_str("b").unwrap(), 5);
        g.merge(&extra, 4, 4).unwrap();
        assert_eq!(2, g.len());
    }

    #[test]
    fn zero_to_zero() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("a").unwrap(), 1);
        g.put(1, Label::from_str("back").unwrap(), 0);
        g.formation(2, &[]);
        g.put(0, Label::from_str("b").unwrap(), 2);
        let mut extra = Sodg::empty(256);
        extra.formation(0, &[]);
        extra.formation(1, &[]);
        extra.put(0, Label::from_str("c").unwrap(), 1);
        extra.put(1, Label::from_str("back").unwrap(), 0);
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(4, g.len());
    }

    #[test]
    fn finds_siblings() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("a").unwrap(), 1);
        g.formation(2, &[]);
        g.put(0, Label::from_str("b").unwrap(), 2);
        let mut extra = Sodg::empty(256);
        extra.formation(0, &[]);
        extra.formation(1, &[]);
        extra.put(0, Label::from_str("b").unwrap(), 1);
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(3, g.len());
    }

    #[test]
    fn merges_kinds_and_lambdas() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        let mut extra = Sodg::empty(256);
        let x = Label::from_str("x").unwrap();
        extra.formation(0, &[x]);
        extra.lambda(0, "L_foo");
        extra.dispatch(1, 0, x);
        extra.put(0, x, 1);
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(&[x], g.attrs(0));
        assert_eq!(Some("L_foo"), g.atom(0));
        let kid = g.kid(0, x).unwrap();
        assert_eq!(Kind::Dispatch(x), g.kind(kid));
        assert_eq!(0, g.kid(kid, Label::Greek('π')).unwrap());
    }

    #[cfg(test)]
    use crate::Script;

    #[test]
    fn two_big_graphs() {
        let mut g: Sodg<16> = Sodg::empty(256);
        Script::from_str(
            "F 0 foo alpha
            F 1 back
            F 2
            P 0 foo 1
            P 0 alpha 1
            P 1 back 0",
        )
        .deploy_to(&mut g)
        .unwrap();
        let mut extra = Sodg::empty(256);
        Script::from_str("F 0 bar\nF 1 back\nP 0 bar 1\nP 1 back 0")
            .deploy_to(&mut extra)
            .unwrap();
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(4, g.len());
    }
}
