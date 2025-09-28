// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use anyhow::Context as _;
#[cfg(debug_assertions)]
use log::trace;

use std::borrow::Cow;
use std::convert::TryFrom as _;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::str::FromStr as _;

use crate::{BRANCH_NONE, BRANCH_STATIC, Edge, EdgeIndex, LabelId, Persistence, Sodg, Vertex};
use crate::{Hex, Label, LabelInterner, LabelInternerError};

#[cfg(test)]
use std::cell::Cell;

#[cfg(test)]
thread_local! {
    static EDGE_COMPARISON_COUNTER: Cell<usize> = Cell::new(0);
}

#[cfg(test)]
fn reset_edge_comparison_counter() {
    EDGE_COMPARISON_COUNTER.with(|counter| counter.set(0));
}

#[cfg(test)]
fn edge_comparison_count() -> usize {
    EDGE_COMPARISON_COUNTER.with(|counter| counter.get())
}

/// Errors that may occur when binding vertices with pre-interned labels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindError {
    /// The provided identifier does not exist in the [`LabelInterner`].
    UnknownLabelId(LabelId),
    /// The label pool exhausted the representable [`LabelId`] range.
    LabelInternerCapacity,
    /// The supplied [`Label`] cannot be represented canonically because it contains an
    /// unsupported character.
    InvalidLabelCharacter(char),
    /// The supplied [`Label`] does not match the canonical representation of the identifier.
    LabelMismatch {
        /// Canonical label stored in the interner.
        expected: Label,
        /// Caller-provided label value.
        provided: Label,
    },
}

impl Display for BindError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::UnknownLabelId(id) => write!(f, "label identifier {id} is not interned"),
            Self::LabelInternerCapacity => f.write_str("label interner capacity exhausted"),
            Self::InvalidLabelCharacter(ch) => {
                write!(f, "label contains unsupported character '{ch}'")
            }
            Self::LabelMismatch { expected, provided } => write!(
                f,
                "label {provided} does not match canonical representation {expected}"
            ),
        }
    }
}

impl std::error::Error for BindError {}

impl From<LabelInternerError> for BindError {
    fn from(error: LabelInternerError) -> Self {
        match error {
            LabelInternerError::CapacityExceeded => Self::LabelInternerCapacity,
            LabelInternerError::InvalidLabelCharacter(symbol) => {
                Self::InvalidLabelCharacter(symbol)
            }
        }
    }
}

impl<const N: usize> Vertex<N> {
    fn update_existing_edge(
        &mut self,
        label_id: LabelId,
        label: Label,
        destination: usize,
    ) -> bool {
        if let Some(edge) = self.edges.iter_mut().find(|edge| {
            #[cfg(test)]
            EDGE_COMPARISON_COUNTER.with(|counter| counter.set(counter.get() + 1));
            edge.label_id == label_id
        }) {
            edge.to = destination;
            edge.label = label;
            true
        } else {
            false
        }
    }

    fn push_edge(&mut self, label_id: LabelId, label: Label, destination: usize) {
        self.edges.push(Edge {
            label_id,
            label,
            to: destination,
        });
    }

    fn update_index(&mut self, label_id: LabelId, destination: u32) -> Option<u32> {
        self.index.insert(label_id, destination)
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

impl<const N: usize> Sodg<N> {
    pub(crate) fn edge_label_text<'a>(&'a self, edge: &'a Edge) -> Cow<'a, str> {
        self.labels
            .resolve(edge.label_id)
            .map_or_else(|| Cow::Owned(edge.label.to_string()), Cow::Borrowed)
    }

    /// Intern the provided [`Label`] within the graph's [`LabelInterner`].
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`LabelInterner::get_or_intern`], namely
    /// [`LabelInternerError::CapacityExceeded`] when the identifier space is
    /// exhausted and [`LabelInternerError::InvalidLabelCharacter`] when the
    /// label cannot be canonicalized into UTF-8 text.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    ///
    /// let mut graph: Sodg<16> = Sodg::empty(16);
    /// graph.add(0);
    /// graph.add(1);
    /// let label = Label::from_str("edge").unwrap();
    /// let id = graph.intern_label(&label).unwrap();
    /// graph.bind_with_label_id(0, 1, id, label).unwrap();
    /// assert_eq!(Some(1), graph.kid(0, Label::from_str("edge").unwrap()));
    /// ```
    pub fn intern_label(&mut self, label: &Label) -> Result<LabelId, LabelInternerError> {
        self.labels.get_or_intern(label)
    }

    /// Retrieve the identifier previously assigned to [`label`](Label) without
    /// mutating the graph.
    ///
    /// Returns [`None`] when the label has not been interned yet.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    ///
    /// let mut graph: Sodg<16> = Sodg::empty(16);
    /// graph.add(0);
    /// graph.add(1);
    /// let label = Label::from_str("edge").unwrap();
    /// let id = graph.intern_label(&label).unwrap();
    /// assert_eq!(Some(id), graph.label_id(&label));
    /// ```
    #[must_use]
    pub fn label_id(&self, label: &Label) -> Option<LabelId> {
        self.labels.lookup(label)
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

    fn collect_branch_members(&mut self, branch: usize) -> Vec<usize> {
        let Some(members) = self.branches.get_mut(branch) else {
            return Vec::new();
        };
        let mut collected = Vec::with_capacity(members.len());
        collected.extend(members.iter().copied());
        members.clear();
        collected.sort_unstable();
        collected.dedup();
        collected
    }

    fn edges_pointing_to(&self, targets: &[usize]) -> Vec<(usize, Vec<(LabelId, usize)>)> {
        if targets.is_empty() {
            return Vec::new();
        }
        let mut removals = Vec::new();
        for (source, vertex) in self.vertices.iter() {
            let mut edges = Vec::new();
            for edge in &vertex.edges {
                if targets.contains(&edge.to) {
                    edges.push((edge.label_id, edge.to));
                }
            }
            if !edges.is_empty() {
                removals.push((source, edges));
            }
        }
        removals
    }

    fn remove_edges(&mut self, removals: &[(usize, Vec<(LabelId, usize)>)]) {
        for (source, edges) in removals {
            if let Some(vertex) = self.vertices.get_mut(*source) {
                for (label_id, _) in edges {
                    vertex.remove_edge(*label_id);
                }
            }
        }
    }

    fn reset_vertices(&mut self, vertices: &[usize]) {
        for vertex_id in vertices {
            if let Some(vertex) = self.vertices.get_mut(*vertex_id) {
                vertex.edges.clear();
                vertex.index = EdgeIndex::new();
                vertex.branch = BRANCH_NONE;
                vertex.persistence = Persistence::Empty;
                vertex.data = Hex::empty();
            }
        }
    }

    fn cleanup_branch(&mut self, branch: usize) -> Vec<usize> {
        let members = self.collect_branch_members(branch);
        if members.is_empty() {
            if let Some(stored) = self.stores.get_mut(branch) {
                *stored = 0;
            }
            return members;
        }
        let removals = self.edges_pointing_to(&members);
        self.remove_edges(&removals);
        self.reset_vertices(&members);
        if let Some(stored) = self.stores.get_mut(branch) {
            *stored = 0;
        }
        members
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
    /// g.bind(0, 42, Label::from_str("hello").unwrap()).unwrap();
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
    /// g.bind(0, 42, Label::from_str("forward").unwrap()).unwrap();
    /// g.bind(42, 0, Label::from_str("backward").unwrap()).unwrap();
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
    /// # Errors
    ///
    /// Returns [`BindError::LabelInternerCapacity`] when the label interner cannot allocate a new
    /// identifier.
    ///
    /// Returns [`BindError::InvalidLabelCharacter`] when the label contains characters that cannot
    /// participate in the canonical UTF-8 representation.
    #[inline]
    pub fn bind(&mut self, v1: usize, v2: usize, a: Label) -> Result<(), BindError> {
        let label_id = self.labels.get_or_intern(&a).map_err(BindError::from)?;
        self.bind_with_label_id(v1, v2, label_id, a)
    }

    /// Bind two vertices using an already interned label identifier.
    ///
    /// This method skips the label interning step, which allows callers to
    /// reuse cached [`LabelId`] values gathered via [`Sodg::intern_label`] or
    /// [`Sodg::label_id`]. It behaves identically to [`bind`](Self::bind)
    /// otherwise.
    ///
    /// # Errors
    ///
    /// Returns [`BindError::UnknownLabelId`] if `label_id` was not interned.
    ///
    /// Returns [`BindError::LabelMismatch`] when `label` does not match the
    /// canonical representation stored in the interner.
    ///
    /// Returns [`BindError::InvalidLabelCharacter`] when `label` contains characters that cannot be
    /// canonicalized.
    ///
    /// # Panics
    ///
    /// Propagates the same panics as [`bind`](Self::bind) when the referenced
    /// vertices are missing or the branches bookkeeping becomes inconsistent.
    #[inline]
    pub fn bind_with_label_id(
        &mut self,
        v1: usize,
        v2: usize,
        label_id: LabelId,
        label: Label,
    ) -> Result<(), BindError> {
        self.bind_preinterned(v1, v2, label_id, label)
    }

    fn bind_preinterned(
        &mut self,
        v1: usize,
        v2: usize,
        label_id: LabelId,
        label: Label,
    ) -> Result<(), BindError> {
        let canonical = self
            .labels
            .canonical_label(label_id)
            .copied()
            .ok_or(BindError::UnknownLabelId(label_id))?;
        let normalized = match LabelInterner::canonicalize(&label) {
            Ok(value) => value,
            Err(LabelInternerError::InvalidLabelCharacter(symbol)) => {
                return Err(BindError::InvalidLabelCharacter(symbol));
            }
            Err(LabelInternerError::CapacityExceeded) => {
                return Err(BindError::LabelInternerCapacity);
            }
        };
        if normalized != canonical {
            return Err(BindError::LabelMismatch {
                expected: canonical,
                provided: label,
            });
        }
        self.bind_canonical(v1, v2, label_id, normalized);
        Ok(())
    }

    fn bind_canonical(&mut self, v1: usize, v2: usize, label_id: LabelId, label: Label) {
        #[cfg(debug_assertions)]
        if let Some(resolved) = self.labels.resolve(label_id) {
            debug_assert_eq!(resolved, label.to_string());
        }
        let mut ours = self.vertices.get(v1).unwrap().branch;
        let theirs = self.vertices.get(v2).unwrap().branch;
        let destination = Self::encode_vertex_id(v2);
        {
            let vertex = self.vertices.get_mut(v1).unwrap();
            let previous = vertex.update_index(label_id, destination);
            if previous.is_some() {
                let updated = vertex.update_existing_edge(label_id, label, v2);
                if !updated {
                    debug_assert!(false, "edge index and adjacency list diverged");
                    vertex.push_edge(label_id, label, v2);
                }
            } else {
                vertex.push_edge(label_id, label, v2);
            }
        }
        let vtx1 = self.vertices.get_mut(v1).unwrap();
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
            label,
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
        enum Retrieval {
            Fresh,
            Repeat,
        }

        let mut cleanup_branch = None;
        let mut retrieved = None;
        let mut result = None;
        {
            let vertex = self.vertices.get_mut(v).unwrap();
            match vertex.persistence {
                Persistence::Stored => {
                    debug_assert!(
                        vertex.branch != BRANCH_NONE,
                        "Vertex ν{v} is marked for storage but has no branch",
                    );
                    let data = vertex.data.clone();
                    vertex.persistence = Persistence::Taken;
                    let branch = vertex.branch;
                    if let Some(stored) = self.stores.get_mut(branch) {
                        debug_assert!(*stored > 0, "Branch {branch} store counter underflow");
                        *stored -= 1;
                        if *stored == 0 {
                            cleanup_branch = Some(branch);
                        }
                    } else {
                        cleanup_branch = Some(branch);
                    }
                    result = Some(data);
                    retrieved = Some(Retrieval::Fresh);
                }
                Persistence::Taken => {
                    result = Some(vertex.data.clone());
                    retrieved = Some(Retrieval::Repeat);
                }
                Persistence::Empty => {}
            }
        }
        if let Some(branch) = cleanup_branch {
            let removed = self.cleanup_branch(branch);
            if !removed.is_empty() {
                #[cfg(debug_assertions)]
                trace!(
                    "#data: branch no.{} destroyed {} vertices as garbage: {}",
                    branch,
                    removed.len(),
                    removed
                        .iter()
                        .map(|vertex| format!("ν{vertex}"))
                        .collect::<Vec<String>>()
                        .join(", "),
                );
            }
        }
        if let Some(retrieval) = retrieved {
            #[cfg(debug_assertions)]
            match retrieval {
                Retrieval::Fresh => trace!("#data: data of ν{v} retrieved"),
                Retrieval::Repeat => trace!("#data: data of ν{v} retrieved again"),
            }
            #[cfg(not(debug_assertions))]
            {
                let _ = retrieval;
            }
        }
        result
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
    /// g.bind(0, 42, Label::from_str("k").unwrap()).unwrap();
    /// let kid = g.kids(0).next().unwrap();
    /// assert_eq!("k", kid.label().to_string());
    /// assert_eq!(42, kid.destination());
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
    /// g.bind(0, 42, Label::from_str("a").unwrap()).unwrap();
    /// g.bind(0, 42, Label::from_str("b").unwrap()).unwrap();
    /// g.bind(0, 42, Label::from_str("c").unwrap()).unwrap();
    /// let mut names = g
    ///     .kids(0)
    ///     .map(|kid| kid.label().to_string())
    ///     .collect::<Vec<String>>();
    /// names.sort();
    /// assert_eq!("a,b,c", names.join(","));
    /// ```
    ///
    /// # Panics
    ///
    /// If vertex `v1` is absent, `Err` will be returned.
    #[inline]
    pub fn kids(&self, v: usize) -> impl Iterator<Item = KidRef<'_>> + '_ {
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
    /// g.bind(0, 42, k).unwrap();
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
    /// g.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
    /// g.bind(1, 2, Label::from_str("bar").unwrap()).unwrap();
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
/// Borrowed view over an outbound edge returned by [`Sodg::kids`].
///
/// # Invariants
///
/// * `label_id` matches the canonical UTF-8 representation of [`label`](Self::label)
///   in the owning [`LabelInterner`].
/// * `destination` always references an existing vertex identifier at the moment
///   the iterator yields the value.
///
/// # Examples
///
/// ```
/// use std::str::FromStr as _;
/// use sodg::{Label, Sodg};
///
/// let mut graph: Sodg<16> = Sodg::empty(16);
/// graph.add(0);
/// graph.add(1);
/// graph.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
/// let kid = graph.kids(0).next().unwrap();
/// assert_eq!("foo", kid.label().to_string());
/// assert_eq!(1, kid.destination());
/// ```
#[derive(Clone, Copy, Debug)]
pub struct KidRef<'a> {
    label_id: LabelId,
    label: &'a Label,
    destination: &'a usize,
}

impl<'a> KidRef<'a> {
    /// Interned identifier that backs the kid's label.
    #[must_use]
    pub const fn label_id(&self) -> LabelId {
        self.label_id
    }

    /// Structured label that decorates the outbound edge.
    #[must_use]
    pub const fn label(&self) -> &'a Label {
        self.label
    }

    /// Identifier of the vertex at the other end of the edge.
    #[must_use]
    pub const fn destination(&self) -> usize {
        *self.destination
    }

    /// Borrowed identifier of the vertex at the other end of the edge.
    #[must_use]
    pub const fn destination_ref(&self) -> &'a usize {
        self.destination
    }
}

/// Owning iterator that powers [`Sodg::kids`].
///
/// The iterator keeps the original [`Edge`] collection and the shared
/// [`LabelInterner`] reference in sync while yielding lightweight [`KidRef`]
/// projections.
struct Kids<'a> {
    interner: &'a LabelInterner,
    inner: std::slice::Iter<'a, Edge>,
}

impl<'a> Iterator for Kids<'a> {
    type Item = KidRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let edge = self.inner.next()?;
        #[cfg(not(debug_assertions))]
        let _ = &self.interner;
        #[cfg(debug_assertions)]
        if let Some(resolved) = self.interner.resolve(edge.label_id) {
            debug_assert_eq!(resolved, edge.label.to_string());
        }
        Some(KidRef {
            label_id: edge.label_id,
            label: &edge.label,
            destination: &edge.to,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use super::*;
    use crate::SMALL_THRESHOLD;

    fn build_vertex_with_degree(count: usize) -> Sodg<64> {
        let mut g: Sodg<64> = Sodg::empty(count + 2);
        g.add(0);
        g.add(1);
        g.add(2);
        for edge in 0..count {
            let destination = edge % 2 + 1;
            g.bind(0, destination, Label::Alpha(edge)).unwrap();
        }
        g
    }

    #[test]
    fn adds_simple_vertex() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::Alpha(0)).unwrap();
        assert_eq!(2, g.len());
    }

    #[test]
    fn sets_branch_correctly() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::Alpha(0)).unwrap();
        assert_eq!(1, g.branches.get(1).unwrap().len());
        assert_eq!(2, g.branches.get(2).unwrap().len());
        g.put(2, &Hex::from(42));
        assert_eq!(&1, g.stores.get(2).unwrap());
        g.add(3);
        g.bind(1, 3, Label::Alpha(1)).unwrap();
        assert_eq!(3, g.branches.get(2).unwrap().len());
        g.add(4);
        g.add(5);
        g.bind(4, 5, Label::Alpha(0)).unwrap();
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
        g.bind(1, 2, k).unwrap();
        assert_eq!(2, g.kid(1, k).unwrap());
    }

    #[test]
    fn binds_two_names() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        let first = Label::from_str("first").unwrap();
        g.bind(1, 2, first).unwrap();
        let second = Label::from_str("second").unwrap();
        g.bind(1, 2, second).unwrap();
        assert_eq!(2, g.kid(1, first).unwrap());
        assert_eq!(2, g.kid(1, second).unwrap());
    }

    #[test]
    fn overwrites_edge() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::from_str("foo").unwrap()).unwrap();
        g.add(3);
        g.bind(1, 3, Label::from_str("foo").unwrap()).unwrap();
        assert_eq!(3, g.kid(1, Label::from_str("foo").unwrap()).unwrap());
    }

    #[test]
    fn binds_to_root() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("x").unwrap()).unwrap();
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
        g.bind(1, 2, Label::Alpha(0)).unwrap();
        g.put(2, &Hex::from_str_bytes("hello"));
        g.add(3);
        g.bind(1, 3, Label::Alpha(0)).unwrap();
        assert_eq!(3, g.len());
        assert_eq!(3, g.branches.get(2).unwrap().len());
        g.data(2);
        assert_eq!(0, g.len());
    }

    #[test]
    fn garbage_collection_cleans_vertices_and_edges() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.add(2);
        g.bind(0, 1, Label::Alpha(0)).unwrap();
        g.bind(1, 2, Label::Alpha(1)).unwrap();
        g.put(2, &Hex::from_str_bytes("payload"));

        assert!(g.kid(0, Label::Alpha(0)).is_some());
        assert!(g.kid(1, Label::Alpha(1)).is_some());

        g.data(2);

        assert!(g.kid(0, Label::Alpha(0)).is_none());
        assert!(g.kid(1, Label::Alpha(1)).is_none());
        assert_eq!(BRANCH_NONE, g.vertices.get(0).unwrap().branch);
        assert_eq!(BRANCH_NONE, g.vertices.get(1).unwrap().branch);
        assert_eq!(BRANCH_NONE, g.vertices.get(2).unwrap().branch);
        assert!(g.vertices.get(0).unwrap().edges.is_empty());
        assert!(g.vertices.get(1).unwrap().edges.is_empty());
        assert!(g.vertices.get(2).unwrap().edges.is_empty());
        assert!(g.vertices.get(0).unwrap().persistence == Persistence::Empty);
        assert!(g.vertices.get(1).unwrap().persistence == Persistence::Empty);
        assert!(g.vertices.get(2).unwrap().persistence == Persistence::Empty);
    }

    #[test]
    fn finds_all_kids() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("one").unwrap()).unwrap();
        g.bind(0, 1, Label::from_str("two").unwrap()).unwrap();
        assert_eq!(2, g.kids(0).count());
        let mut names = vec![];
        for kid in g.kids(0) {
            names.push(format!("{}/{}", kid.label(), kid.destination()));
        }
        names.sort();
        assert_eq!("one/1,two/1", names.join(","));
    }

    #[test]
    fn builds_list_of_kids() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("one").unwrap()).unwrap();
        g.bind(0, 1, Label::from_str("two").unwrap()).unwrap();
        g.bind(0, 1, Label::from_str("three").unwrap()).unwrap();
        let mut names: Vec<String> = g.kids(0).map(|kid| format!("{}", kid.label())).collect();
        names.sort();
        assert_eq!("one,three,two", names.join(","));
    }

    #[test]
    fn grows_branch_beyond_inline_capacity() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        for vertex in 1..=20 {
            g.add(vertex);
            g.bind(0, vertex, Label::Alpha(vertex)).unwrap();
        }
        let branch = g.vertices.get(0).unwrap().branch;
        let members = g.branches.get(branch).unwrap();
        assert!(members.len() > 16);
        assert!(members.contains(&20));
    }

    #[test]
    fn kid_handles_single_edge_vertex() {
        let g = build_vertex_with_degree(1);
        let vertex = g.vertices.get(0).unwrap();
        assert!(matches!(vertex.index, EdgeIndex::Small(_)));
        assert_eq!(Some(1), g.kid(0, Label::Alpha(0)));
    }

    #[test]
    fn kid_handles_degree_just_below_threshold() {
        let g = build_vertex_with_degree(SMALL_THRESHOLD - 1);
        let vertex = g.vertices.get(0).unwrap();
        assert!(matches!(vertex.index, EdgeIndex::Small(_)));
        let label = Label::Alpha(SMALL_THRESHOLD - 2);
        let expected = (SMALL_THRESHOLD - 2) % 2 + 1;
        assert_eq!(Some(expected), g.kid(0, label));
    }

    #[test]
    fn kid_handles_degree_past_threshold() {
        let g = build_vertex_with_degree(SMALL_THRESHOLD + 1);
        let vertex = g.vertices.get(0).unwrap();
        assert!(matches!(vertex.index, EdgeIndex::Large(_)));
        let label = Label::Alpha(SMALL_THRESHOLD);
        let expected = SMALL_THRESHOLD % 2 + 1;
        assert_eq!(Some(expected), g.kid(0, label));
    }

    #[test]
    fn bind_with_preinterned_label_id_skips_interner() {
        let mut g: Sodg<16> = Sodg::empty(16);
        g.add(0);
        g.add(1);
        let label = Label::Alpha(7);
        assert!(g.label_id(&label).is_none());
        let label_id = g.intern_label(&label).unwrap();
        assert_eq!(Some(label_id), g.label_id(&label));
        assert!(g.bind_with_label_id(0, 1, label_id, label).is_ok());
        assert_eq!(Some(1), g.kid(0, label));
    }

    #[test]
    fn bind_with_preinterned_label_id_rejects_unknown_identifier() {
        let mut g: Sodg<16> = Sodg::empty(16);
        g.add(0);
        g.add(1);
        let error = g
            .bind_with_label_id(0, 1, 99, Label::Alpha(0))
            .expect_err("unknown label id must yield an error");
        assert!(matches!(error, BindError::UnknownLabelId(99)));
    }

    #[test]
    fn bind_with_preinterned_label_id_validates_canonical_label() {
        let mut g: Sodg<16> = Sodg::empty(16);
        g.add(0);
        g.add(1);
        let canonical = Label::from_str("edge").unwrap();
        let label_id = g.intern_label(&canonical).unwrap();
        let mismatched = Label::Alpha(7);
        let error = g
            .bind_with_label_id(0, 1, label_id, mismatched)
            .expect_err("mismatched label must be rejected");
        assert!(matches!(
            error,
            BindError::LabelMismatch {
                expected,
                provided,
            } if expected == canonical && provided == mismatched
        ));
    }

    #[test]
    fn bind_rejects_labels_with_non_ascii_characters() {
        let mut g: Sodg<16> = Sodg::empty(16);
        g.add(0);
        g.add(1);
        let label = Label::from_str("λβ").unwrap();
        let error = g
            .bind(0, 1, label)
            .expect_err("labels containing unsupported characters must be rejected");
        assert!(matches!(error, BindError::InvalidLabelCharacter('λ')));
    }

    #[test]
    fn bind_with_label_id_propagates_invalid_character_errors() {
        let mut g: Sodg<16> = Sodg::empty(16);
        g.add(0);
        g.add(1);
        let canonical = Label::from_str("edge").unwrap();
        let label_id = g.intern_label(&canonical).unwrap();
        let invalid = Label::from_str("λβ").unwrap();
        let error = g
            .bind_with_label_id(0, 1, label_id, invalid)
            .expect_err("invalid characters must be reported consistently");
        assert!(matches!(error, BindError::InvalidLabelCharacter('λ')));
    }

    #[test]
    fn bind_with_preinterned_label_id_accepts_equivalent_text_with_spaces() {
        let mut g: Sodg<16> = Sodg::empty(16);
        g.add(0);
        g.add(1);
        let spaced = Label::from_str("foo bar").unwrap();
        let canonical = LabelInterner::canonicalize(&spaced).unwrap();
        let label_id = g.intern_label(&spaced).unwrap();
        g.bind_with_label_id(0, 1, label_id, spaced)
            .expect("label containing spaces must bind successfully");
        assert_eq!(Some(1), g.kid(0, Label::from_str("foo bar").unwrap()));
        let vertex = g.vertices.get(0).unwrap();
        let edge = vertex
            .edges
            .iter()
            .find(|edge| edge.label_id == label_id)
            .expect("bound edge must exist");
        assert_eq!(canonical, edge.label);
    }

    #[test]
    fn bind_with_preinterned_label_id_rejects_incorrect_text_after_normalization() {
        let mut g: Sodg<16> = Sodg::empty(16);
        g.add(0);
        g.add(1);
        let spaced = Label::from_str("foo bar").unwrap();
        let canonical = LabelInterner::canonicalize(&spaced).unwrap();
        let label_id = g.intern_label(&spaced).unwrap();
        let mismatched = Label::from_str("foo baz").unwrap();
        let error = g
            .bind_with_label_id(0, 1, label_id, mismatched)
            .expect_err("mismatched label must still be rejected");
        assert!(matches!(
            error,
            BindError::LabelMismatch {
                expected,
                provided,
            } if expected == canonical && provided == mismatched
        ));
    }

    #[test]
    fn bind_updates_existing_edge_with_canonical_label() {
        let mut g: Sodg<16> = Sodg::empty(16);
        g.add(0);
        g.add(1);
        g.add(2);
        let padded = Label::Str(['f', 'o', 'o', ' ', ' ', ' ', ' ', ' ']);
        let canonical = Label::from_str("foo").unwrap();
        let label_id = g.intern_label(&padded).unwrap();
        g.bind_with_label_id(0, 1, label_id, padded)
            .expect("initial bind must succeed");
        g.bind_with_label_id(0, 2, label_id, canonical)
            .expect("rebinding must succeed");
        let vertex = g.vertices.get(0).unwrap();
        let edge = vertex
            .edges
            .iter()
            .find(|edge| edge.label_id == label_id)
            .expect("edge must exist");
        assert_eq!(canonical, edge.label);
        assert_eq!(2, edge.to);
    }

    #[test]
    fn binds_many_unique_labels_preserves_destinations() {
        const EDGE_COUNT: usize = 256;
        let mut g: Sodg<16> = Sodg::empty(EDGE_COUNT * 2 + 4);
        g.add(0);
        for label_idx in 0..EDGE_COUNT {
            let destination = label_idx + 1;
            g.add(destination);
            g.bind(0, destination, Label::Alpha(label_idx)).unwrap();
        }
        for label_idx in 0..EDGE_COUNT {
            assert_eq!(Some(label_idx + 1), g.kid(0, Label::Alpha(label_idx)));
        }
    }

    #[test]
    fn rebinding_small_index_edges_is_linear() {
        let mut g: Sodg<64> = Sodg::empty(SMALL_THRESHOLD * 2 + 4);
        g.add(0);
        for label_idx in 0..SMALL_THRESHOLD {
            let destination = label_idx + 1;
            g.add(destination);
            g.bind(0, destination, Label::Alpha(label_idx)).unwrap();
        }
        assert!(matches!(
            g.vertices.get(0).unwrap().index,
            EdgeIndex::Small(_)
        ));
        super::reset_edge_comparison_counter();
        assert_eq!(0, super::edge_comparison_count());
        for label_idx in 0..SMALL_THRESHOLD {
            let before = super::edge_comparison_count();
            let new_destination = SMALL_THRESHOLD + 1 + label_idx;
            g.add(new_destination);
            g.bind(0, new_destination, Label::Alpha(label_idx)).unwrap();
            let after = super::edge_comparison_count();
            assert_eq!(label_idx + 1, after - before);
            assert_eq!(Some(new_destination), g.kid(0, Label::Alpha(label_idx)));
        }
        assert!(matches!(
            g.vertices.get(0).unwrap().index,
            EdgeIndex::Small(_)
        ));
    }

    #[test]
    fn remove_edge_from_small_index_keeps_structures_in_sync() {
        let mut g = build_vertex_with_degree(3);
        let label = Label::Alpha(1);
        let label_id = g.labels.lookup(&label).unwrap();
        {
            let vertex = g.vertices.get_mut(0).unwrap();
            let previous = vertex.edges.len();
            let removed = vertex.remove_edge(label_id).unwrap();
            assert_eq!(label_id, removed.label_id);
            assert_eq!(2, removed.to);
            assert_eq!(previous - 1, vertex.edges.len());
            assert_eq!(vertex.edges.len(), vertex.index.len());
            assert!(matches!(vertex.index, EdgeIndex::Small(_)));
        }
        assert!(g.kid(0, label).is_none());
    }

    #[test]
    fn remove_edge_from_large_index_keeps_structures_in_sync() {
        let mut g = build_vertex_with_degree(SMALL_THRESHOLD + 2);
        let label = Label::Alpha(1);
        let label_id = g.labels.lookup(&label).unwrap();
        {
            let vertex = g.vertices.get_mut(0).unwrap();
            assert!(matches!(vertex.index, EdgeIndex::Large(_)));
            let previous = vertex.edges.len();
            let removed = vertex.remove_edge(label_id).unwrap();
            assert_eq!(label_id, removed.label_id);
            assert_eq!(2, removed.to);
            assert_eq!(previous - 1, vertex.edges.len());
            assert_eq!(vertex.edges.len(), vertex.index.len());
        }
        assert!(matches!(
            g.vertices.get(0).unwrap().index,
            EdgeIndex::Large(_)
        ));
        assert!(g.kid(0, label).is_none());
    }

    #[test]
    fn find_traverses_long_path_and_detects_breaks() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let labels = ["s0", "s1", "s2", "s3", "s4"];
        for vertex in 0..=labels.len() {
            g.add(vertex);
        }
        for (idx, text) in labels.iter().enumerate() {
            g.bind(
                idx,
                idx + 1,
                Label::from_str(text).expect("valid label for traversal test"),
            )
            .unwrap();
        }
        assert_eq!(Some(labels.len()), g.find(0, "s0.s1.s2.s3.s4"));
        assert!(g.find(0, "s0.s1.s2.s3.missing").is_none());
        assert!(g.find(0, "s0.s1..s3").is_none());
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
        g.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
        g.bind(1, 2, Label::from_str("bar").unwrap()).unwrap();
        assert_eq!(Some(2), g.find(0, "foo.bar"));
        assert_eq!(Some(1), g.find(0, "foo"));
        assert_eq!(Some(0), g.find(0, ""));
    }

    #[test]
    fn find_stops_on_missing_segment() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
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
