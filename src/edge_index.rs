// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

//! Per-vertex index of departing edges.

use itertools::Either;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

use crate::LabelId;

/// Maps the identifier of an edge label to the vertex the edge points at.
///
/// Most vertices have a handful of edges, where a linear scan over a flat
/// array beats hashing. Some vertices have many, where the scan turns into
/// the bottleneck. The index starts flat, in the `Small` shape backed by
/// [`micromap::Map`], and switches to the `Large` shape backed by a hash map
/// once more than `N` distinct labels depart from the vertex.
#[derive(Serialize, Deserialize, Clone)]
pub enum EdgeIndex<const N: usize> {
    Small(micromap::Map<LabelId, usize, N>),
    Large(FxHashMap<LabelId, usize>),
}

impl<const N: usize> Default for EdgeIndex<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> EdgeIndex<N> {
    /// Make an empty index, in its flat shape.
    pub const fn new() -> Self {
        Self::Small(micromap::Map::new())
    }

    /// Return the vertex the labelled edge points at.
    pub fn get(&self, label: LabelId) -> Option<usize> {
        match self {
            Self::Small(map) => map.get(&label).copied(),
            Self::Large(map) => map.get(&label).copied(),
        }
    }

    /// Point the labelled edge at the vertex, replacing the previous target
    /// of the same label.
    ///
    /// The index grows into its hashed shape when the flat one is full and
    /// the label is not in it yet.
    pub fn insert(&mut self, label: LabelId, to: usize) {
        match self {
            Self::Small(map) => {
                if map.checked_insert(label, to).is_none() {
                    let mut grown: FxHashMap<LabelId, usize> =
                        map.iter().map(|(l, v)| (*l, *v)).collect();
                    grown.insert(label, to);
                    *self = Self::Large(grown);
                }
            }
            Self::Large(map) => {
                map.insert(label, to);
            }
        }
    }

    /// Iterate over the edges, in no particular order.
    pub fn iter(&self) -> impl Iterator<Item = (&LabelId, &usize)> + '_ {
        match self {
            Self::Small(map) => Either::Left(map.iter()),
            Self::Large(map) => Either::Right(map.iter()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn starts_empty() {
        let index: EdgeIndex<4> = EdgeIndex::new();
        assert_eq!(0, index.iter().count());
    }

    #[test]
    fn finds_nothing_in_an_empty_index() {
        let index: EdgeIndex<4> = EdgeIndex::new();
        assert_eq!(None, index.get(1));
    }

    #[test]
    fn keeps_a_single_edge() {
        let mut index: EdgeIndex<4> = EdgeIndex::new();
        index.insert(1, 42);
        assert_eq!(Some(42), index.get(1));
    }

    #[test]
    fn overwrites_an_edge() {
        let mut index: EdgeIndex<4> = EdgeIndex::new();
        index.insert(1, 42);
        index.insert(1, 13);
        assert_eq!(Some(13), index.get(1));
        assert_eq!(1, index.iter().count());
    }

    #[test]
    fn stays_flat_until_it_is_full() {
        let mut index: EdgeIndex<4> = EdgeIndex::new();
        for label in 1..=4 {
            index.insert(label, usize::try_from(label).unwrap());
        }
        assert!(matches!(index, EdgeIndex::Small(_)));
    }

    #[test]
    fn grows_when_the_flat_shape_is_full() {
        let mut index: EdgeIndex<4> = EdgeIndex::new();
        for label in 1..=5 {
            index.insert(label, usize::try_from(label).unwrap());
        }
        assert!(matches!(index, EdgeIndex::Large(_)));
    }

    #[test]
    fn keeps_every_edge_while_growing() {
        let mut index: EdgeIndex<4> = EdgeIndex::new();
        for label in 1..=32 {
            index.insert(label, usize::try_from(label).unwrap());
        }
        for label in 1..=32 {
            assert_eq!(Some(usize::try_from(label).unwrap()), index.get(label));
        }
        assert_eq!(32, index.iter().count());
    }

    #[test]
    fn overwrites_an_edge_after_growing() {
        let mut index: EdgeIndex<2> = EdgeIndex::new();
        for label in 1..=4 {
            index.insert(label, usize::try_from(label).unwrap());
        }
        index.insert(1, 99);
        assert_eq!(Some(99), index.get(1));
        assert_eq!(4, index.iter().count());
    }

    #[test]
    fn does_not_grow_when_a_full_index_is_overwritten() {
        let mut index: EdgeIndex<2> = EdgeIndex::new();
        index.insert(1, 1);
        index.insert(2, 2);
        index.insert(1, 3);
        assert!(matches!(index, EdgeIndex::Small(_)));
        assert_eq!(Some(3), index.get(1));
    }
}
