// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::{HashMap, HashSet};

use anyhow::{anyhow, bail, Context, Result};
use log::debug;

use crate::{Label, LabelId, Persistence, Sodg};

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
        let mut label_mappings = HashMap::new();
        let before = self.len();
        self.merge_rec(g, left, right, &mut mapped, &mut label_mappings)?;
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

    /// Merge two trees recursively, ignoring nodes already in `mapped`.
    ///
    /// `right` vertex (from `g`) is mapped onto `left` vertex (in `self`).
    /// Children decisions are made recursively.
    ///
    /// `mapped`: key is a vertex from the right graph, value is the mapped vertex in the left graph.
    ///
    /// # Errors
    /// Returns an error if merge is impossible (e.g., missing vertex).
    #[allow(clippy::option_if_let_else)]
    fn merge_rec(
        &mut self,
        g: &Self,
        left: usize,
        right: usize,
        mapped: &mut HashMap<usize, usize>,
        label_mappings: &mut HashMap<LabelId, (LabelId, Label)>,
    ) -> Result<()> {
        // If already mapped, nothing to do
        if mapped.contains_key(&right) {
            return Ok(());
        }

        // Record mapping early to avoid cycles re-entering here
        mapped.insert(right, left);

        // Access vertex safely
        let v = g
            .vertices
            .get(right)
            .with_context(|| format!("Can't find ν{right}"))?;

        // Merge payload if present
        if v.persistence != Persistence::Empty {
            // put: merges data from right into left
            self.put(left, &v.data);
        }
        for kid in g.kids(right) {
            let label = *kid.label();
            let destination = kid.destination();
            let matched = if let Some(t) = self.kid(left, label) {
                t
            } else {
                let (label_id, canonical_label) =
                    self.resolve_label_mapping(label_mappings, kid.label_id(), label)?;
                if let Some(t) = mapped.get(&destination) {
                    self.bind_with_label_id(left, *t, label_id, canonical_label)?;
                    *t
                } else {
                    let id = self.next_id();
                    self.add(id);
                    self.bind_with_label_id(left, id, label_id, canonical_label)?;
                    id
                }
            };
            self.merge_rec(g, matched, destination, mapped, label_mappings)?;
        }
        for kid in g.kids(right) {
            let label = *kid.label();
            let destination = kid.destination();
            if let Some(first) = self.kid(left, label)
                && let Some(second) = mapped.get(&destination)
                && first != *second
            {
                self.join(first, *second)?;
            }
        }

        Ok(())
    }

    fn join(&mut self, left: usize, right: usize) -> Result<()> {
        for v in self.keys() {
            let targets = self.vertices.get(v).map_or_else(Vec::new, |vertex| {
                vertex
                    .edges
                    .iter()
                    .filter(|edge| edge.to == right)
                    .map(|edge| edge.label_id)
                    .collect::<Vec<_>>()
            });
            for label_id in targets {
                self.update_edge_destination(v, label_id, left);
            }
        }
        let kids = self
            .vertices
            .get(right)
            .map(|vertex| {
                vertex
                    .edges
                    .iter()
                    .map(|edge| (edge.label_id, edge.label, edge.to))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        for (label_id, label, destination) in kids {
            assert!(
                self.kid(left, label).is_none(),
                "Can't merge ν{right} into ν{left}, due to conflict in '{}'",
                self.labels
                    .resolve(label_id)
                    .map_or_else(|| label.to_string(), str::to_owned),
            );
            let canonical = self.canonical_label(label_id)?;
            self.bind_with_label_id(left, destination, label_id, canonical)?;
        }
        self.vertices.remove(right);
        Ok(())
    }

    fn resolve_label_mapping(
        &mut self,
        cache: &mut HashMap<LabelId, (LabelId, Label)>,
        source_label_id: LabelId,
        label: Label,
    ) -> Result<(LabelId, Label)> {
        if let Some(&(mapped_id, mapped_label)) = cache.get(&source_label_id) {
            return Ok((mapped_id, mapped_label));
        }
        let label_id = if let Some(existing) = self.label_id(&label) {
            existing
        } else {
            self.intern_label(&label)?
        };
        let canonical = self.canonical_label(label_id)?;
        cache.insert(source_label_id, (label_id, canonical));
        Ok((label_id, canonical))
    }

    fn canonical_label(&self, label_id: LabelId) -> Result<Label> {
        self.labels
            .canonical_label(label_id)
            .copied()
            .ok_or_else(|| anyhow!("label identifier {label_id} is not interned"))
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use super::*;
    use crate::Label;

    fn assert_edges_accessible(graph: &Sodg<16>) {
        for vertex in graph.keys() {
            for kid in graph.kids(vertex) {
                let label = *kid.label();
                assert_eq!(
                    kid.destination(),
                    graph.kid(vertex, label).unwrap_or_else(|| panic!(
                        "edge '{}' from ν{vertex} is unreachable",
                        label.to_string()
                    )),
                );
            }
        }
    }

    #[test]
    fn merges_two_graphs() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("bar").unwrap()).unwrap();
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(3, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
        assert_eq!(2, g.kid(0, Label::from_str("bar").unwrap()).unwrap());
        assert_edges_accessible(&g);
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
    fn reports_missing_vertex() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        let mut extra = Sodg::empty(2);
        let missing = 1;
        extra.vertices.remove(missing);
        let error = g.merge(&extra, 0, missing).unwrap_err();
        let message = error.to_string();
        let expected = format!("Can't find ν{missing}");
        assert!(message.contains(&expected), "{message}");
    }

    #[test]
    fn merges_a_loop() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("a").unwrap()).unwrap();
        g.add(2);
        g.bind(1, 2, Label::from_str("b").unwrap()).unwrap();
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(4);
        extra.bind(0, 4, Label::from_str("c").unwrap()).unwrap();
        extra.add(3);
        extra.bind(0, 3, Label::from_str("a").unwrap()).unwrap();
        extra.bind(4, 3, Label::from_str("d").unwrap()).unwrap();
        extra.add(5);
        extra.bind(3, 5, Label::from_str("e").unwrap()).unwrap();
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(5, g.len());
        let a_label = Label::from_str("a").unwrap();
        let b_label = Label::from_str("b").unwrap();
        let c_label = Label::from_str("c").unwrap();
        let d_label = Label::from_str("d").unwrap();
        let e_label = Label::from_str("e").unwrap();
        let a_child = g.kid(0, a_label).unwrap();
        let c_child = g.kid(0, c_label).unwrap();
        assert_eq!(2, g.kid(a_child, b_label).unwrap());
        let via_d = g.kid(c_child, d_label).unwrap();
        assert_eq!(a_child, via_d);
        let leaf = g.kid(a_child, e_label).unwrap();
        assert_eq!(leaf, g.kid(via_d, e_label).unwrap());
        assert_edges_accessible(&g);
    }

    #[test]
    fn avoids_simple_duplicates() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(5);
        g.bind(0, 5, Label::from_str("foo").unwrap()).unwrap();
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
        extra.add(2);
        extra.bind(1, 2, Label::from_str("bar").unwrap()).unwrap();
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(3, g.len());
        assert_eq!(5, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
        assert_eq!(1, g.kid(5, Label::from_str("bar").unwrap()).unwrap());
        assert_edges_accessible(&g);
    }

    #[test]
    fn keeps_existing_vertices_intact() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
        g.add(2);
        g.bind(1, 2, Label::from_str("bar").unwrap()).unwrap();
        g.add(3);
        g.bind(2, 3, Label::from_str("zzz").unwrap()).unwrap();
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(5);
        extra.bind(0, 5, Label::from_str("foo").unwrap()).unwrap();
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(4, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
        assert_eq!(2, g.kid(1, Label::from_str("bar").unwrap()).unwrap());
        assert_eq!(3, g.kid(2, Label::from_str("zzz").unwrap()).unwrap());
        assert_edges_accessible(&g);
    }

    #[test]
    fn merges_singletons() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(13);
        let mut extra = Sodg::empty(256);
        extra.add(13);
        g.merge(&extra, 13, 13).unwrap();
        assert_eq!(1, g.len());
        assert_edges_accessible(&g);
    }

    #[test]
    fn merges_simple_loop() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::from_str("foo").unwrap()).unwrap();
        g.bind(2, 1, Label::from_str("bar").unwrap()).unwrap();
        let extra = g.clone();
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(extra.len(), g.len());
        assert_edges_accessible(&g);
    }

    #[test]
    fn merges_large_loop() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.add(3);
        g.add(4);
        g.bind(1, 2, Label::from_str("a").unwrap()).unwrap();
        g.bind(2, 3, Label::from_str("b").unwrap()).unwrap();
        g.bind(3, 4, Label::from_str("c").unwrap()).unwrap();
        g.bind(4, 1, Label::from_str("d").unwrap()).unwrap();
        let extra = g.clone();
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(extra.len(), g.len());
        assert_edges_accessible(&g);
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
        assert_edges_accessible(&g);
    }

    #[test]
    fn understands_same_name_kids() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("a").unwrap()).unwrap();
        g.add(2);
        g.bind(1, 2, Label::from_str("x").unwrap()).unwrap();
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("b").unwrap()).unwrap();
        extra.add(2);
        extra.bind(1, 2, Label::from_str("x").unwrap()).unwrap();
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(5, g.len());
        assert_eq!(1, g.kid(0, Label::from_str("a").unwrap()).unwrap());
        assert_eq!(2, g.kid(1, Label::from_str("x").unwrap()).unwrap());
        assert_edges_accessible(&g);
    }

    #[test]
    fn merges_into_empty_graph() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        let mut extra = Sodg::empty(256);
        extra.add(1);
        extra.add(2);
        extra.add(3);
        extra.bind(1, 2, Label::from_str("a").unwrap()).unwrap();
        extra.bind(2, 3, Label::from_str("b").unwrap()).unwrap();
        extra.bind(3, 1, Label::from_str("c").unwrap()).unwrap();
        g.merge(&extra, 1, 1).unwrap();
        assert_eq!(3, g.len());
        let loop_target = g.kid(1, Label::from_str("a").unwrap()).unwrap();
        assert_ne!(1, loop_target);
        assert_edges_accessible(&g);
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
        extra.bind(4, 5, Label::from_str("b").unwrap()).unwrap();
        g.merge(&extra, 4, 4).unwrap();
        assert_eq!(2, g.len());
        assert_edges_accessible(&g);
    }

    #[test]
    fn zero_to_zero() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("a").unwrap()).unwrap();
        g.bind(1, 0, Label::from_str("back").unwrap()).unwrap();
        g.add(2);
        g.bind(0, 2, Label::from_str("b").unwrap()).unwrap();
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("c").unwrap()).unwrap();
        extra.bind(1, 0, Label::from_str("back").unwrap()).unwrap();
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(4, g.len());
        assert_edges_accessible(&g);
    }

    #[test]
    fn finds_siblings() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("a").unwrap()).unwrap();
        g.add(2);
        g.bind(0, 2, Label::from_str("b").unwrap()).unwrap();
        let mut extra = Sodg::empty(256);
        extra.add(0);
        extra.add(1);
        extra.bind(0, 1, Label::from_str("b").unwrap()).unwrap();
        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(3, g.len());
        assert_edges_accessible(&g);
    }

    #[test]
    fn merges_wide_graph() {
        let mut g: Sodg<16> = Sodg::empty(512);
        g.add(0);

        let mut extra = Sodg::empty(512);
        extra.add(0);
        let sink = 100;
        extra.add(sink);
        let sink_label = Label::from_str("sink").unwrap();
        let width: usize = 12;
        for edge in 0..width {
            let child = edge + 1;
            extra.add(child);
            extra.bind(0, child, Label::Alpha(edge)).unwrap();
            extra.bind(child, sink, sink_label).unwrap();
        }

        g.merge(&extra, 0, 0).unwrap();
        assert_eq!(width + 2, g.len());
        let mut seen_sink = None;
        for edge in 0..width {
            let child = g.kid(0, Label::Alpha(edge)).unwrap();
            let target = g.kid(child, sink_label).unwrap();
            match seen_sink {
                Some(expected) => assert_eq!(expected, target),
                None => seen_sink = Some(target),
            }
        }
        assert_edges_accessible(&g);
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
        assert_edges_accessible(&g);
    }
}
