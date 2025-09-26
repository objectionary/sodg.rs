// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use anyhow::Context as _;
#[cfg(debug_assertions)]
use log::trace;

use std::borrow::Cow;
use std::convert::TryFrom as _;
use std::str::FromStr as _;

use crate::{BRANCH_NONE, BRANCH_STATIC, Edge, LabelId, Persistence, Sodg, Vertex};
use crate::{Hex, Label, LabelInterner};

impl<const N: usize> Vertex<N> {
    fn upsert_edge(&mut self, label_id: LabelId, label: Label, destination: usize) {
        if let Some(edge) = self.edges.iter_mut().find(|edge| edge.label_id == label_id) {
            edge.to = destination;
            edge.label = label;
        } else {
            self.edges.push(Edge {
                label_id,
                label,
                to: destination,
            });
        }
    }

    fn update_index(&mut self, label_id: LabelId, destination: u32) {
        self.index.insert(label_id, destination);
    }

    pub(crate) fn rebuild_index(&mut self) {
        let pairs = self
            .edges
            .iter()
            .map(|edge| (edge.label_id, Sodg::<N>::encode_vertex_id(edge.to)));
        self.index.rebuild(pairs);
    }

    #[allow(dead_code)]
    fn remove_edge(&mut self, label_id: LabelId) -> Option<Edge> {
        let position = self
            .edges
            .iter()
            .position(|edge| edge.label_id == label_id)?;
        self.index.remove(label_id);
        Some(self.edges.remove(position))
    }

    fn get_destination(&self, label_id: LabelId) -> Option<u32> {
        self.index.get(label_id)
    }
}

impl LabelInterner {
    fn lookup(&self, label: &Label) -> Option<LabelId> {
        self.get(label)
    }

    fn ensure_id(&mut self, label: &Label) -> LabelId {
        self.get_or_intern(label)
            .expect("label interner capacity exhausted")
    }
}

impl<const N: usize> Sodg<N> {
    pub(crate) fn edge_label_text<'a>(&'a self, edge: &'a Edge) -> Cow<'a, str> {
        self.labels
            .resolve(edge.label_id)
            .map_or_else(|| Cow::Owned(edge.label.to_string()), Cow::Borrowed)
    }

    fn encode_vertex_id(vertex: usize) -> u32 {
        u32::try_from(vertex).expect("vertex identifier exceeds u32 range")
    }

    fn decode_vertex_id(vertex: u32) -> usize {
        usize::try_from(vertex).expect("vertex identifier exceeds usize range")
    }

    pub(crate) fn update_edge_destination(
        &mut self,
        source: usize,
        label_id: LabelId,
        destination: usize,
    ) {
        if let Some(vertex) = self.vertices.get_mut(source)
            && let Some(edge) = vertex
                .edges
                .iter_mut()
                .find(|edge| edge.label_id == label_id)
        {
            edge.to = destination;
            vertex
                .index
                .insert(label_id, Self::encode_vertex_id(destination));
        }
    }
}

impl<const N: usize> Sodg<N> {
    /// Add a new vertex `v1` to itself.
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(0);
    /// g.add(42);
    /// g.bind(0, 42, Label::from_str("hello").unwrap());
    /// ```
    ///
    /// If vertex `v1` already exists in the graph, nothing will happen.
    ///
    /// # Panics
    ///
    /// If alerts trigger any error, the error will be returned here.
    #[inline]
    pub fn add(&mut self, v1: usize) {
        self.vertices.get_mut(v1).unwrap().branch = 1;
        #[cfg(debug_assertions)]
        trace!("#add: vertex ν{v1} added");
    }

    /// Make an edge `e1` from vertex `v1` to vertex `v2` and put `a` label on it.
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(0);
    /// g.add(42);
    /// g.bind(0, 42, Label::from_str("forward").unwrap());
    /// g.bind(42, 0, Label::from_str("backward").unwrap());
    /// ```
    ///
    /// If an edge with this label already exists, it will be replaced with a new edge.
    ///
    /// # Panics
    ///
    /// If either vertex `v1` or `v2` is absent, an `Err` will be returned.
    ///
    /// If `v1` equals to `v2`, an `Err` will be returned.
    ///
    /// The label `a` can't be empty. If it is empty, an `Err` will be returned.
    ///
    /// If alerts trigger any error, the error will be returned here.
    #[inline]
    pub fn bind(&mut self, v1: usize, v2: usize, a: Label) {
        let mut ours = self.vertices.get(v1).unwrap().branch;
        let theirs = self.vertices.get(v2).unwrap().branch;
        let label_id = self.labels.ensure_id(&a);
        let destination = Self::encode_vertex_id(v2);
        let vtx1 = self.vertices.get_mut(v1).unwrap();
        vtx1.upsert_edge(label_id, a, v2);
        vtx1.update_index(label_id, destination);
        if ours == BRANCH_STATIC {
            if theirs == BRANCH_STATIC {
                for b in self.branches.iter_mut() {
                    if b.1.is_empty() {
                        b.1.push(v1);
                        ours = b.0;
                        vtx1.branch = ours;
                        break;
                    }
                }
                self.vertices.get_mut(v2).unwrap().branch = ours;
                self.branches.get_mut(ours).unwrap().push(v2);
            } else {
                vtx1.branch = theirs;
                self.branches.get_mut(theirs).unwrap().push(v1);
            }
        } else {
            let vtx2 = self.vertices.get_mut(v2).unwrap();
            if vtx2.branch == BRANCH_STATIC {
                vtx2.branch = ours;
                self.branches.get_mut(ours).unwrap().push(v2);
            }
        }
        #[cfg(debug_assertions)]
        trace!(
            "#bind: edge added ν{}(b={}).{} → ν{}(b={})",
            v1,
            self.vertices.get(v1).unwrap().branch,
            a,
            v2,
            self.vertices.get(v2).unwrap().branch,
        );
    }

    /// Set vertex data.
    ///
    /// For example:
    ///
    /// ```
    /// use sodg::Hex;
    /// use sodg::Sodg;
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(42);
    /// g.put(42, &Hex::from_str_bytes("hello, world!"));
    /// ```
    ///
    /// # Panics
    ///
    /// If vertex `v1` is absent, an `Err` will be returned.
    ///
    /// If alerts trigger any error, the error will be returned here.
    #[inline]
    pub fn put(&mut self, v: usize, d: &Hex) {
        let vtx = self.vertices.get_mut(v).unwrap();
        vtx.persistence = Persistence::Stored;
        vtx.data = d.clone();
        *self.stores.get_mut(vtx.branch).unwrap() += 1;
        #[cfg(debug_assertions)]
        trace!("#put: data of ν{v} set to {d}");
    }

    /// Read vertex data, and then submit the vertex to garbage collection.
    ///
    /// For example:
    ///
    /// ```
    /// use sodg::Hex;
    /// use sodg::Sodg;
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(42);
    /// let data = Hex::from_str_bytes("hello, world!");
    /// g.put(42, &data);
    /// assert_eq!(data, g.data(42).unwrap());
    /// ```
    ///
    /// If there is no data, `None` will be returned, for example:
    ///
    /// ```
    /// use sodg::Sodg;
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(42);
    /// assert!(g.data(42).is_none());
    /// ```
    ///
    /// # Panics
    ///
    /// If vertex `v1` is absent, it will panic.
    #[inline]
    pub fn data(&mut self, v: usize) -> Option<Hex> {
        let vtx = self.vertices.get_mut(v).unwrap();
        match vtx.persistence {
            Persistence::Stored => {
                let d = vtx.data.clone();
                vtx.persistence = Persistence::Taken;
                let branch = vtx.branch;
                let s = self.stores.get_mut(branch).unwrap();
                *s -= 1;
                if *s == 0 {
                    let members = self.branches.get_mut(branch).unwrap();
                    for v in members.into_iter() {
                        self.vertices.get_mut(v).unwrap().branch = BRANCH_NONE;
                    }
                    #[cfg(debug_assertions)]
                    trace!(
                        "#data: branch no.{} destroyed {} vertices as garbage: {}",
                        branch,
                        members.len(),
                        members
                            .into_iter()
                            .map(|v| format!("ν{v}"))
                            .collect::<Vec<String>>()
                            .join(", ")
                    );
                    members.clear();
                }
                #[cfg(debug_assertions)]
                trace!("#data: data of ν{v} retrieved");
                Some(d)
            }
            Persistence::Taken => {
                #[cfg(debug_assertions)]
                trace!("#data: data of ν{v} retrieved again");
                Some(vtx.data.clone())
            }
            Persistence::Empty => None,
        }
    }

    /// Find all kids of a vertex.
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(0);
    /// g.add(42);
    /// g.bind(0, 42, Label::from_str("k").unwrap());
    /// let (a, to) = g.kids(0).next().unwrap().clone();
    /// assert_eq!("k", a.to_string());
    /// assert_eq!(42, *to);
    /// ```
    ///
    /// Just in case, if you need to put all names into a single line:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use itertools::Itertools;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(0);
    /// g.add(42);
    /// g.bind(0, 42, Label::from_str("a").unwrap());
    /// g.bind(0, 42, Label::from_str("b").unwrap());
    /// g.bind(0, 42, Label::from_str("c").unwrap());
    /// let mut names = g.kids(0).into_iter().map(|(a, _)| a.to_string()).collect::<Vec<String>>();
    /// names.sort();
    /// assert_eq!("a,b,c", names.join(","));
    /// ```
    ///
    /// # Panics
    ///
    /// If vertex `v1` is absent, `Err` will be returned.
    #[inline]
    pub fn kids(&self, v: usize) -> impl Iterator<Item = (&Label, &usize)> + '_ {
        let vertex = self
            .vertices
            .get(v)
            .with_context(|| format!("Can't find ν{v} in kids()"))
            .unwrap();
        Kids {
            interner: &self.labels,
            inner: vertex.edges.iter(),
        }
    }

    /// Find a kid of a vertex, by its edge name, and return the ID of the vertex found.
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(0);
    /// g.add(42);
    /// let k = Label::from_str("k").unwrap();
    /// g.bind(0, 42, k);
    /// assert_eq!(42, g.kid(0, k).unwrap());
    /// ```
    ///
    /// # Panics
    ///
    /// If vertex `v1` is absent, it will panic.
    #[must_use]
    #[inline]
    pub fn kid(&self, v: usize, a: Label) -> Option<usize> {
        let label_id = self.labels.lookup(&a)?;
        let vertex = self.vertices.get(v)?;
        let destination = vertex.get_destination(label_id)?;
        Some(Self::decode_vertex_id(destination))
    }

    /// Find a vertex by walking the provided locator from `start`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(0);
    /// g.add(1);
    /// g.add(2);
    /// g.bind(0, 1, Label::from_str("foo").unwrap());
    /// g.bind(1, 2, Label::from_str("bar").unwrap());
    /// assert_eq!(Some(2), g.find(0, "foo.bar"));
    /// assert_eq!(None, g.find(0, "foo.baz"));
    /// ```
    #[must_use]
    pub fn find(&self, start: usize, locator: &str) -> Option<usize> {
        if locator.is_empty() {
            return Some(start);
        }
        let mut current = start;
        for segment in locator.split('.') {
            if segment.is_empty() {
                return None;
            }
            let label = Label::from_str(segment).ok()?;
            current = self.kid(current, label)?;
        }
        Some(current)
    }
}

/// Iterator returned by [`Sodg::kids`] that yields outbound edges and their destinations.
struct Kids<'a> {
    interner: &'a LabelInterner,
    inner: std::slice::Iter<'a, Edge>,
}

impl<'a> Iterator for Kids<'a> {
    type Item = (&'a Label, &'a usize);

    fn next(&mut self) -> Option<Self::Item> {
        let edge = self.inner.next()?;
        #[cfg(debug_assertions)]
        if let Some(resolved) = self.interner.resolve(edge.label_id) {
            debug_assert_eq!(resolved, edge.label.to_string());
        }
        Some((&edge.label, &edge.to))
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use super::*;

    #[test]
    fn adds_simple_vertex() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::Alpha(0));
        assert_eq!(2, g.len());
    }

    #[test]
    fn sets_branch_correctly() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::Alpha(0));
        assert_eq!(1, g.branches.get(1).unwrap().len());
        assert_eq!(2, g.branches.get(2).unwrap().len());
        g.put(2, &Hex::from(42));
        assert_eq!(&1, g.stores.get(2).unwrap());
        g.add(3);
        g.bind(1, 3, Label::Alpha(1));
        assert_eq!(3, g.branches.get(2).unwrap().len());
        g.add(4);
        g.add(5);
        g.bind(4, 5, Label::Alpha(0));
        assert_eq!(2, g.branches.get(3).unwrap().len());
        g.data(2);
        assert_eq!(0, g.branches.get(2).unwrap().len());
    }

    #[test]
    fn fetches_kid() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        let k = Label::from_str("hello").unwrap();
        g.bind(1, 2, k);
        assert_eq!(2, g.kid(1, k).unwrap());
    }

    #[test]
    fn binds_two_names() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        let first = Label::from_str("first").unwrap();
        g.bind(1, 2, first);
        let second = Label::from_str("second").unwrap();
        g.bind(1, 2, second);
        assert_eq!(2, g.kid(1, first).unwrap());
        assert_eq!(2, g.kid(1, second).unwrap());
    }

    #[test]
    fn overwrites_edge() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::from_str("foo").unwrap());
        g.add(3);
        g.bind(1, 3, Label::from_str("foo").unwrap());
        assert_eq!(3, g.kid(1, Label::from_str("foo").unwrap()).unwrap());
    }

    #[test]
    fn binds_to_root() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("x").unwrap());
        assert!(g.kid(0, Label::from_str("ρ").unwrap()).is_none());
        assert!(g.kid(0, Label::from_str("σ").unwrap()).is_none());
    }

    #[test]
    fn sets_simple_data() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let data = Hex::from_str_bytes("hello");
        g.add(0);
        g.put(0, &data);
        assert_eq!(data, g.data(0).unwrap());
    }

    #[test]
    fn collects_garbage() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::Alpha(0));
        g.put(2, &Hex::from_str_bytes("hello"));
        g.add(3);
        g.bind(1, 3, Label::Alpha(0));
        assert_eq!(3, g.len());
        assert_eq!(3, g.branches.get(2).unwrap().len());
        g.data(2);
        assert_eq!(0, g.len());
    }

    #[test]
    fn finds_all_kids() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("one").unwrap());
        g.bind(0, 1, Label::from_str("two").unwrap());
        assert_eq!(2, g.kids(0).count());
        let mut names = vec![];
        for (a, to) in g.kids(0) {
            names.push(format!("{a}/{to}"));
        }
        names.sort();
        assert_eq!("one/1,two/1", names.join(","));
    }

    #[test]
    fn builds_list_of_kids() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("one").unwrap());
        g.bind(0, 1, Label::from_str("two").unwrap());
        g.bind(0, 1, Label::from_str("three").unwrap());
        let mut names: Vec<String> = g.kids(0).map(|(a, _)| format!("{a}")).collect();
        names.sort();
        assert_eq!("one,three,two", names.join(","));
    }

    #[test]
    fn gets_data_from_empty_vertex() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        assert!(g.data(0).is_none());
    }

    #[test]
    fn gets_absent_kid() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        assert!(g.kid(0, Label::from_str("hello").unwrap()).is_none());
    }

    #[test]
    fn gets_kid_from_absent_vertex() {
        let g: Sodg<16> = Sodg::empty(256);
        assert!(g.kid(0, Label::from_str("hello").unwrap()).is_none());
    }

    #[test]
    fn finds_vertices_by_locator() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.add(2);
        g.bind(0, 1, Label::from_str("foo").unwrap());
        g.bind(1, 2, Label::from_str("bar").unwrap());
        assert_eq!(Some(2), g.find(0, "foo.bar"));
        assert_eq!(Some(1), g.find(0, "foo"));
        assert_eq!(Some(0), g.find(0, ""));
    }

    #[test]
    fn find_stops_on_missing_segment() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap());
        assert!(g.find(0, "foo.bar").is_none());
        assert!(g.find(0, "..foo").is_none());
    }

    #[test]
    fn adds_twice() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(0);
    }
}
