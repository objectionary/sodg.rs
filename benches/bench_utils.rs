// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

//! Shared helpers for Criterion and Callgrind benchmark suites.

#![allow(dead_code)]

use std::fmt::Write as _;

use sodg::{EdgeIndex, EdgeIndexEntry, Label, LabelId, Sodg};

/// Benchmark degrees that exercise both variants of [`EdgeIndex`].
pub(crate) const BENCHMARK_DEGREES: [usize; 5] = [1, 31, 32, 33, 64];

/// Generate sequential [`LabelId`] values for a vertex with `degree` outbound edges.
#[must_use]
pub(crate) fn label_ids_for_degree(degree: usize) -> Vec<LabelId> {
    (0..degree).map(|value| value as LabelId).collect()
}

/// Populate `index` with destinations derived from `labels`.
pub(crate) fn populate_edge_index(index: &mut EdgeIndex, labels: &[LabelId]) {
    for (offset, label) in labels.iter().enumerate() {
        let destination = (offset + 1) as u32;
        index.insert(*label, EdgeIndexEntry { destination, slot: offset });
    }
}

/// Build a fully populated [`EdgeIndex`] that stores all `labels`.
#[must_use]
pub(crate) fn build_edge_index(labels: &[LabelId]) -> EdgeIndex {
    let mut index = EdgeIndex::new();
    populate_edge_index(&mut index, labels);
    index
}

/// Insert edges for the provided `degree` and return the populated [`EdgeIndex`].
#[must_use]
pub(crate) fn run_edge_index_inserts(degree: usize) -> EdgeIndex {
    let labels = label_ids_for_degree(degree);
    build_edge_index(&labels)
}

/// Remove edges for the provided `degree` and return the number of removed entries.
#[must_use]
pub(crate) fn run_edge_index_removals(degree: usize) -> usize {
    let labels = label_ids_for_degree(degree);
    let mut index = build_edge_index(&labels);
    labels.iter().filter(|&&label| index.remove(label).is_some()).count()
}

/// Perform lookups for the provided `degree` and return the number of successful hits.
#[must_use]
pub(crate) fn run_edge_index_lookups(degree: usize) -> usize {
    let labels = label_ids_for_degree(degree);
    let index = build_edge_index(&labels);
    labels.iter().filter(|&&label| index.get(label).is_some()).count()
}

/// Build a graph where every vertex on the hot path has `degree` outbound edges.
#[must_use]
pub(crate) fn dense_graph_with_locator<const N: usize>(
    degree: usize,
    depth: usize,
) -> (Sodg<N>, String) {
    let effective_degree = degree.max(1);
    let total_vertices = depth * effective_degree;
    let mut graph = Sodg::<N>::empty(total_vertices + 1);
    for vertex in 0..=total_vertices {
        graph.add(vertex);
    }
    let mut next_vertex = 1usize;
    let mut current = 0usize;
    let mut locator = String::new();
    for segment in 0..depth {
        let main_label = Label::Alpha(segment);
        graph.bind(current, next_vertex, main_label).unwrap();
        if !locator.is_empty() {
            locator.push('.');
        }
        // Labels implement `Display`, but repeated allocations for `format!` would be costly.
        // Reuse the same buffer to avoid temporary `String`s.
        let _ = write!(locator, "{}", main_label);
        for filler in 1..degree {
            let filler_label = Label::Alpha(segment + filler * depth);
            graph.bind(current, next_vertex + filler, filler_label).unwrap();
        }
        current = next_vertex;
        next_vertex += degree.max(1);
    }
    (graph, locator)
}
