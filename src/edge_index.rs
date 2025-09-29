// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

//! Adaptive index for outbound edges.
//!
//! The [`EdgeIndex`] starts with a compact [`micromap::Map`] for graphs with a
//! small number of unique labels and automatically promotes itself to a standard
//! [`std::collections::HashMap`] once the number of tracked labels exceeds the
//! predefined [`SMALL_THRESHOLD`]. This keeps lookups efficient without paying
//! the hash-map overhead for the common, tiny vertex case.

use std::{collections::HashMap, hash::BuildHasherDefault};

use serde::{Deserialize, Serialize};

use rustc_hash::FxHasher;

use crate::{Label, LabelId};

type LargeIndexMap = HashMap<LabelId, EdgeIndexEntry, BuildHasherDefault<FxHasher>>;

/// Compact entry stored by [`EdgeIndex`].
///
/// The `destination` field keeps the encoded vertex identifier while `slot`
/// points at the corresponding [`Edge`](crate::Edge) stored inside the owning
/// vertex adjacency list.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct EdgeIndexEntry {
    /// Encoded identifier of the destination vertex.
    pub destination: u32,
    /// Slot of the matching [`Edge`](crate::Edge) within `Vertex::edges`.
    pub slot: usize,
}

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
/// use sodg::{EdgeIndex, EdgeIndexEntry, SMALL_THRESHOLD};
///
/// let mut index = EdgeIndex::new();
/// assert!(index.is_empty());
/// let entry = EdgeIndexEntry { destination: 42, slot: 0 };
/// index.insert(1, entry);
/// assert_eq!(Some(entry), index.get(1));
/// for (slot_offset, label) in (2..=u32::try_from(SMALL_THRESHOLD).unwrap()).enumerate() {
///     index.insert(
///         label,
///         EdgeIndexEntry {
///             destination: label.saturating_mul(2),
///             slot: slot_offset + 1,
///         },
///     );
/// }
/// assert!(index.len() >= SMALL_THRESHOLD);
/// ```
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum EdgeIndex {
    /// Compact representation backed by [`micromap::Map`].
    Small(micromap::Map<LabelId, EdgeIndexEntry, SMALL_THRESHOLD>),
    /// Hash-based representation that handles arbitrarily many labels using [`FxHasher`].
    Large(LargeIndexMap),
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
    pub fn get(&self, label: LabelId) -> Option<EdgeIndexEntry> {
        match self {
            Self::Small(map) => map.get(&label).copied(),
            Self::Large(map) => map.get(&label).copied(),
        }
    }

    /// Retrieve a mutable view of the entry associated with `label`.
    pub fn get_mut(&mut self, label: LabelId) -> Option<&mut EdgeIndexEntry> {
        match self {
            Self::Small(map) => map.get_mut(&label),
            Self::Large(map) => map.get_mut(&label),
        }
    }

    /// Insert a new mapping, returning the previous value if it existed.
    pub fn insert(&mut self, label: LabelId, entry: EdgeIndexEntry) -> Option<EdgeIndexEntry> {
        match self {
            Self::Small(map) => {
                if map.len() == SMALL_THRESHOLD && map.get(&label).is_none() {
                    let current_len = map.len();
                    let expected_capacity =
                        current_len.saturating_mul(2).max(current_len.saturating_add(1));
                    let mut promoted = LargeIndexMap::with_capacity_and_hasher(
                        expected_capacity,
                        BuildHasherDefault::<FxHasher>::default(),
                    );
                    for (stored_label, stored_entry) in map.iter() {
                        promoted.insert(*stored_label, *stored_entry);
                    }
                    promoted.insert(label, entry);
                    let remaining_capacity = expected_capacity.saturating_sub(promoted.len());
                    if remaining_capacity > 0 {
                        let _ = promoted.try_reserve(remaining_capacity);
                    }
                    *self = Self::Large(promoted);
                    None
                } else {
                    map.insert(label, entry)
                }
            }
            Self::Large(map) => map.insert(label, entry),
        }
    }

    /// Remove the mapping associated with `label`.
    pub fn remove(&mut self, label: LabelId) -> Option<EdgeIndexEntry> {
        match self {
            Self::Small(map) => map.remove(&label),
            Self::Large(map) => map.remove(&label),
        }
    }

    /// Populate the index using entries produced by `pairs`.
    pub fn rebuild<I>(&mut self, pairs: I)
    where
        I: IntoIterator<Item = (LabelId, EdgeIndexEntry)>,
    {
        *self = Self::default();
        for (label, entry) in pairs {
            self.insert(label, entry);
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
        let entry = EdgeIndexEntry { destination: 7, slot: 0 };
        assert_eq!(None, index.insert(1, entry));
        assert_eq!(Some(entry), index.get(1));
        assert_eq!(1, index.len());
    }

    #[test]
    fn promotes_once_threshold_exceeded() {
        let mut index = EdgeIndex::new();
        let threshold = u32::try_from(SMALL_THRESHOLD).expect("SMALL_THRESHOLD fits into u32");
        for label in 0..threshold {
            index.insert(
                label,
                EdgeIndexEntry {
                    destination: label + 1,
                    slot: usize::try_from(label).expect("label fits into usize"),
                },
            );
        }
        assert!(matches!(index, EdgeIndex::Small(_)));
        let promoted_entry = EdgeIndexEntry {
            destination: 99,
            slot: usize::try_from(threshold).expect("label fits into usize"),
        };
        index.insert(threshold, promoted_entry);
        assert!(matches!(index, EdgeIndex::Large(_)));
        assert_eq!(Some(promoted_entry), index.get(threshold));
    }

    #[test]
    fn removes_entries_in_both_variants() {
        let mut index = EdgeIndex::new();
        index.insert(1, EdgeIndexEntry { destination: 2, slot: 0 });
        assert_eq!(Some(EdgeIndexEntry { destination: 2, slot: 0 }), index.remove(1));
        assert_eq!(None, index.remove(1));
        let threshold = u32::try_from(SMALL_THRESHOLD).expect("SMALL_THRESHOLD fits into u32");
        index.rebuild((0..=threshold).map(|label| {
            (
                label,
                EdgeIndexEntry {
                    destination: label + 1,
                    slot: usize::try_from(label).expect("label fits into usize"),
                },
            )
        }));
        assert!(matches!(index, EdgeIndex::Large(_)));
        assert_eq!(Some(EdgeIndexEntry { destination: 2, slot: 1 }), index.remove(1));
        assert_eq!(None, index.get(1));
    }

    #[test]
    fn maintains_correct_representation_around_promotion_boundary() {
        for degree in 30..=40 {
            let mut index = EdgeIndex::new();
            let degree_u32 = u32::try_from(degree).expect("degree fits into u32");
            for label in 0..degree_u32 {
                index.insert(
                    label,
                    EdgeIndexEntry {
                        destination: label + 1,
                        slot: usize::try_from(label).expect("label fits into usize"),
                    },
                );
            }
            if degree <= SMALL_THRESHOLD {
                assert!(matches!(index, EdgeIndex::Small(_)), "degree {degree} should stay small");
            } else {
                assert!(matches!(index, EdgeIndex::Large(_)), "degree {degree} should promote");
            }
            for label in 0..degree_u32 {
                assert_eq!(
                    Some(EdgeIndexEntry {
                        destination: label + 1,
                        slot: usize::try_from(label).expect("label fits into usize"),
                    }),
                    index.get(label)
                );
            }
        }
    }

    #[test]
    fn continues_to_accept_inserts_after_promotion() {
        let mut index = EdgeIndex::new();
        let threshold = u32::try_from(SMALL_THRESHOLD).expect("SMALL_THRESHOLD fits into u32");
        for label in 0..=threshold {
            index.insert(
                label,
                EdgeIndexEntry {
                    destination: label + 1,
                    slot: usize::try_from(label).expect("label fits into usize"),
                },
            );
        }
        assert!(matches!(index, EdgeIndex::Large(_)));
        for label in (threshold + 1)..(threshold + 40) {
            index.insert(
                label,
                EdgeIndexEntry {
                    destination: label + 1,
                    slot: usize::try_from(label).expect("label fits into usize"),
                },
            );
        }
        for label in 0..(threshold + 40) {
            assert_eq!(
                Some(EdgeIndexEntry {
                    destination: label + 1,
                    slot: usize::try_from(label).expect("label fits into usize"),
                }),
                index.get(label)
            );
        }
    }
}
