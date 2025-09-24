// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::{HashMap, HashSet};

use anyhow::{Result, bail};
use log::debug;

use crate::{Label, Persistence, Sodg};

impl<const N: usize> Sodg<N> {
    /// Merge another graph into the current one.
    ///
    /// It is expected that both graphs are trees! If they are not, the result is unpredictable.
    ///
    /// The `right` vertex is mapped to the `left` vertex. The decisions about
    /// their kids are made recursively.
    ///
    /// The `left` vertex is expected
    /// to be the root of the current graph, while the `right` vertex is the root
    /// of the graph being merged into the current one.
    ///
    /// # Errors
    ///
    /// If it's impossible to merge, an error will be returned.
    pub fn merge(&mut self, g: &Self, left: usize, right: usize) -> Result<()> {
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
                "Just {merged} vertices merged, out of {scope} (must={}, seen={}); maybe the right graph was not a tree? {} missed: {}",
                must.len(),
                seen.len(),
                ordered.len(),
                ordered
                    .iter()
                    .map(|v| format!("ν{v}"))
                    .collect::<Vec<String>>()
                    .join(", "),
            );
        }
        debug!(
            "Merged all {merged} vertices into SODG of {}, making it have {} after the merge",
            before,
            self.len(),
        );
        Ok(())
    }

    /// Merge two trees recursively, ignoring the nodes already `mapped`.
    ///
    /// The `right` vertex is mapped to the `left` vertex. The decisions about
    /// their kids are made recursively.
    ///
    /// The `mapped` is a key-value map, where the key is a vertex from the right
    /// graph, which is mapped to a vertex from the left graph.
    ///
    /// # Errors
    ///
    /// If it's impossible to merge, an error will be returned.
    #[allow(clippy::option_if_let_else)]
    fn merge_rec(
        &mut self,
        g: &Self,
        left: usize,
        right: usize,
        mapped: &mut HashMap<usize, usize>,
    ) -> Result<()> {
        if mapped.contains_key(&right) {
            return Ok(());
        }
        mapped.insert(right, left);
        if g.vertices.get(right).unwrap().persistence != Persistence::Empty {
            self.put(left, &g.vertices.get(right).unwrap().data);
        }
        for (a, to) in g.kids(right) {
            let matched = if let Some(t) = self.kid(left, *a) {
                t
            } else if let Some(t) = mapped.get(to) {
                self.bind(left, *t, *a);
                *t
            } else {
                let id = self.next_id();
                self.add(id);
                self.bind(left, id, *a);
                id
            };
            self.merge_rec(g, matched, *to, mapped)?;
        }
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
            let mut nv = self.vertices.get(v).unwrap().clone();
            for e in &self.vertices.get_mut(v).unwrap().edges {
                if *e.1 == right {
                    nv.edges.insert(*e.0, left);
                }
            }
            self.vertices.insert(v, nv);
        }
        let kids = self
            .kids(right)
            .map(|(a, v)| (*a, *v))
            .collect::<Vec<(Label, usize)>>();
        for e in kids {
            assert!(
                self.kid(left, e.0).is_none(),
                "Can't merge ν{right} into ν{left}, due to conflict in '{}'",
                e.0,
            );
            self.bind(left, e.1, e.0);
        }
        self.vertices.remove(right);
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use super::*;

    #[test]
    fn merges_two_graphs() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap());
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("bar").unwrap());
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(3, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
        assert_eq!(2, g.kid(0, Label::from_str("bar").unwrap()).unwrap());
    }

    #[test]
    fn merges_two_non_trees() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(42);
        extra.add(2);
        extra.add(13);
        let r = g.merge(&extra, 0, 0);
        assert!(r.is_err());
        let msg = r.err().unwrap().to_string();
        assert!(msg.contains("ν2, ν13, ν42"), "{}", msg);
    }

    #[test]
    fn merges_a_loop() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("a").unwrap());
        g.add(2);
        g.bind(1, 2, Label::from_str("b").unwrap());
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(4);
        extra.bind(0, 4, Label::from_str("c").unwrap());
        extra.add(3);
        extra.bind(0, 3, Label::from_str("a").unwrap());
        extra.bind(4, 3, Label::from_str("d").unwrap());
        extra.add(5);
        extra.bind(3, 5, Label::from_str("e").unwrap());
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
        g.add(0);
        g.add(5);
        g.bind(0, 5, Label::from_str("foo").unwrap());
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("foo").unwrap());
        extra.add(2);
        extra.bind(1, 2, Label::from_str("bar").unwrap());
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(3, g.len());
        assert_eq!(5, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
        assert_eq!(1, g.kid(5, Label::from_str("bar").unwrap()).unwrap());
    }

    #[test]
    fn keeps_existing_vertices_intact() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap());
        g.add(2);
        g.bind(1, 2, Label::from_str("bar").unwrap());
        g.add(3);
        g.bind(2, 3, Label::from_str("zzz").unwrap());
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(5);
        extra.bind(0, 5, Label::from_str("foo").unwrap());
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(4, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
        assert_eq!(2, g.kid(1, Label::from_str("bar").unwrap()).unwrap());
        assert_eq!(3, g.kid(2, Label::from_str("zzz").unwrap()).unwrap());
    }

    #[test]
    fn merges_singletons() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(13);
        let mut extra = Sodg::empty(256);
        extra.add(13);
        g.merge(&extra, 13, 13).unwrap();
        assert_eq!(1, g.len());
    }

    #[test]
    fn merges_simple_loop() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::from_str("foo").unwrap());
        g.bind(2, 1, Label::from_str("bar").unwrap());
        let extra = g.clone();
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(extra.len(), g.len());
    }

    #[test]
    fn merges_large_loop() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.add(3);
        g.add(4);
        g.bind(1, 2, Label::from_str("a").unwrap());
        g.bind(2, 3, Label::from_str("b").unwrap());
        g.bind(3, 4, Label::from_str("c").unwrap());
        g.bind(4, 1, Label::from_str("d").unwrap());
        let extra = g.clone();
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(extra.len(), g.len());
    }

    #[cfg(test)]
    use crate::Hex;

    #[test]
    fn merges_data() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        let mut extra = Sodg::empty(256);
        extra.add(1);
        extra.put(1, &Hex::from(42_i64));
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(42, g.data(1).unwrap().to_i64().unwrap());
    }

    #[test]
    fn understands_same_name_kids() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("a").unwrap());
        g.add(2);
        g.bind(1, 2, Label::from_str("x").unwrap());
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("b").unwrap());
        extra.add(2);
        extra.bind(1, 2, Label::from_str("x").unwrap());
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(5, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("a").unwrap()).unwrap());
        assert_eq!(2, g.kid(1, Label::from_str("x").unwrap()).unwrap());
    }

    #[test]
    fn merges_into_empty_graph() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        let mut extra = Sodg::empty(256);
        extra.add(1);
        extra.add(2);
        extra.add(3);
        extra.bind(1, 2, Label::from_str("a").unwrap());
        extra.bind(2, 3, Label::from_str("b").unwrap());
        extra.bind(3, 1, Label::from_str("c").unwrap());
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(3, g.len());
        assert_eq!(0, g.kid(1, Label::from_str("a").unwrap()).unwrap());
    }

    #[test]
    fn mixed_injection() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(4);
        let mut extra = Sodg::empty(256);
        extra.add(4);
        extra.put(4, &Hex::from(4));
        extra.add(5);
        extra.put(5, &Hex::from(5));
        extra.bind(4, 5, Label::from_str("b").unwrap());
        g.merge(&extra, 4, 4).unwrap();
        assert_eq!(2, g.len());
    }

    #[test]
    fn zero_to_zero() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("a").unwrap());
        g.bind(1, 0, Label::from_str("back").unwrap());
        g.add(2);
        g.bind(0, 2, Label::from_str("b").unwrap());
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("c").unwrap());
        extra.bind(1, 0, Label::from_str("back").unwrap());
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(4, g.len());
    }

    #[test]
    fn finds_siblings() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("a").unwrap());
        g.add(2);
        g.bind(0, 2, Label::from_str("b").unwrap());
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("b").unwrap());
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(3, g.len());
    }

    #[cfg(test)]
    use crate::Script;

    #[test]
    fn two_big_graphs() {
        let mut g: Sodg<16> = Sodg::empty(256);
        Script::from_str(
            "ADD(0); ADD(1); BIND(0, 1, foo);
            ADD(2); BIND(0, 1, alpha);
            BIND(1, 0, back);",
        )
        .deploy_to(&mut g)
        .unwrap();
        let mut extra = Sodg::empty(256);
        Script::from_str("ADD(0); ADD(1); BIND(0, 1, bar); BIND(1, 0, back);")
            .deploy_to(&mut extra)
            .unwrap();
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(4, g.len());
    }
}
