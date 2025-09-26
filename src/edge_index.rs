// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

//! Adaptive index for outbound edges.
//!
//! The [`EdgeIndex`] starts with a compact [`micromap::Map`] for graphs with a
//! small number of unique labels and automatically promotes itself to a standard
//! [`std::collections::HashMap`] once the number of tracked labels exceeds the
//! predefined [`SMALL_THRESHOLD`]. This keeps lookups efficient without paying
//! the hash-map overhead for the common, tiny vertex case.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::{Label, LabelId};

/// Edge metadata stored on every vertex.
///
/// The struct keeps the [`Label`] used at the API boundary together with its
/// interned [`LabelId`] and the destination vertex identifier. The `to` field is
/// represented as [`usize`] to remain compatible with the public graph API,
/// while the [`EdgeIndex`] converts the value to `u32` internally to stay
/// compact.
///
/// # Invariants
///
/// * `label_id` always corresponds to the canonical UTF-8 form of `label` in
///   the owning [`LabelInterner`](crate::LabelInterner).
/// * `to` stores the public vertex identifier; `EdgeIndex` is responsible for
///   encoding the same value into its compact `u32` representation.
///
/// # Examples
///
/// ```
/// use sodg::{Edge, Label};
///
/// let edge = Edge { label_id: 1, label: Label::Alpha(0), to: 2 };
/// assert_eq!(1, edge.label_id);
/// assert_eq!("α0", edge.label.to_string());
/// assert_eq!(2, edge.to);
/// ```
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Edge {
    /// Interned identifier of the edge label.
    pub label_id: LabelId,
    /// Original structured label value.
    pub label: Label,
    /// Destination vertex identifier.
    pub to: usize,
}

/// Maximum number of entries stored in the small-map representation before the
/// index promotes itself to a [`HashMap`].
pub const SMALL_THRESHOLD: usize = 32;

/// Index structure that maps labels to destination vertex identifiers.
///
/// The index starts with a fixed-capacity [`micromap::Map`] to avoid heap
/// allocations in the common small case. Once the number of tracked labels
/// exceeds [`crate::SMALL_THRESHOLD`], the index promotes itself to
/// a [`HashMap`].
///
/// # Invariants
///
/// * Entries in the index always mirror the set of [`Edge`] values stored on
///   the owning vertex.
/// * All stored vertex identifiers are the result of the crate-internal
///   `encode_vertex_id` helper and must be decoded before being exposed publicly.
///
/// # Examples
///
/// ```
/// use sodg::{EdgeIndex, SMALL_THRESHOLD};
///
/// let mut index = EdgeIndex::new();
/// assert!(index.is_empty());
/// index.insert(1, 42);
/// assert_eq!(Some(42), index.get(1));
/// for label in 2..=u32::try_from(SMALL_THRESHOLD).unwrap() {
///     index.insert(label, label.saturating_mul(2));
/// }
/// assert!(index.len() >= SMALL_THRESHOLD);
/// ```
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum EdgeIndex {
    /// Compact representation backed by [`micromap::Map`].
    Small(micromap::Map<LabelId, u32, SMALL_THRESHOLD>),
    /// Hash-based representation that handles arbitrarily many labels.
    Large(HashMap<LabelId, u32>),
}

impl Default for EdgeIndex {
    fn default() -> Self {
        Self::Small(micromap::Map::new())
    }
}

impl EdgeIndex {
    /// Create an empty index.
    #[must_use]
    pub const fn new() -> Self {
        Self::Small(micromap::Map::new())
    }

    /// Current number of tracked entries.
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            Self::Small(map) => map.len(),
            Self::Large(map) => map.len(),
        }
    }

    /// Return `true` if the index does not store any entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Retrieve the stored vertex identifier associated with `label`.
    #[must_use]
    pub fn get(&self, label: LabelId) -> Option<u32> {
        match self {
            Self::Small(map) => map.get(&label).copied(),
            Self::Large(map) => map.get(&label).copied(),
        }
    }

    /// Insert a new mapping, returning the previous value if it existed.
    pub fn insert(&mut self, label: LabelId, vertex: u32) -> Option<u32> {
        match self {
            Self::Small(map) => {
                if map.len() == SMALL_THRESHOLD && map.get(&label).is_none() {
                    let mut promoted = HashMap::with_capacity(map.len() + 1);
                    for (stored_label, stored_vertex) in map.iter() {
                        promoted.insert(*stored_label, *stored_vertex);
                    }
                    promoted.insert(label, vertex);
                    *self = Self::Large(promoted);
                    None
                } else {
                    map.insert(label, vertex)
                }
            }
            Self::Large(map) => map.insert(label, vertex),
        }
    }

    /// Remove the mapping associated with `label`.
    pub fn remove(&mut self, label: LabelId) -> Option<u32> {
        match self {
            Self::Small(map) => map.remove(&label),
            Self::Large(map) => map.remove(&label),
        }
    }

    /// Populate the index using entries produced by `pairs`.
    pub fn rebuild<I>(&mut self, pairs: I)
    where
        I: IntoIterator<Item = (LabelId, u32)>,
    {
        *self = Self::default();
        for (label, vertex) in pairs {
            self.insert(label, vertex);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inserts_and_retrieves_entries() {
        let mut index = EdgeIndex::new();
        assert_eq!(0, index.len());
        assert_eq!(None, index.insert(1, 7));
        assert_eq!(Some(7), index.get(1));
        assert_eq!(1, index.len());
    }

    #[test]
    fn promotes_once_threshold_exceeded() {
        let mut index = EdgeIndex::new();
        let threshold = u32::try_from(SMALL_THRESHOLD).expect("SMALL_THRESHOLD fits into u32");
        for label in 0..threshold {
            index.insert(label, label + 1);
        }
        assert!(matches!(index, EdgeIndex::Small(_)));
        index.insert(threshold, 99);
        assert!(matches!(index, EdgeIndex::Large(_)));
        assert_eq!(Some(99), index.get(threshold));
    }

    #[test]
    fn removes_entries_in_both_variants() {
        let mut index = EdgeIndex::new();
        index.insert(1, 2);
        assert_eq!(Some(2), index.remove(1));
        assert_eq!(None, index.remove(1));
        let threshold = u32::try_from(SMALL_THRESHOLD).expect("SMALL_THRESHOLD fits into u32");
        index.rebuild((0..=threshold).map(|label| (label, label + 1)));
        assert!(matches!(index, EdgeIndex::Large(_)));
        assert_eq!(Some(2), index.remove(1));
        assert_eq!(None, index.get(1));
    }
}
