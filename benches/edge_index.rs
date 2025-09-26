// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

#![cfg_attr(not(feature = "callgrind"), allow(dead_code))]

#[cfg(feature = "callgrind")]
mod bench_utils;

#[cfg(feature = "callgrind")]
use bench_utils::{
    dense_graph_with_locator, run_edge_index_inserts, run_edge_index_lookups,
    run_edge_index_removals,
};

#[cfg(feature = "callgrind")]
use iai_callgrind::{LibraryBenchmarkConfig, library_benchmark, library_benchmark_group, main};

#[cfg(feature = "callgrind")]
const FIND_DEPTH: usize = 4;

#[cfg(feature = "callgrind")]
fn edge_index_insert_len(degree: usize) -> usize {
    run_edge_index_inserts(degree).len()
}

#[cfg(feature = "callgrind")]
fn edge_index_remove_count(degree: usize) -> usize {
    run_edge_index_removals(degree)
}

#[cfg(feature = "callgrind")]
fn edge_index_lookup_count(degree: usize) -> usize {
    run_edge_index_lookups(degree)
}

#[cfg(feature = "callgrind")]
fn find_locator_hit(degree: usize) -> Option<usize> {
    let (graph, locator) = dense_graph_with_locator::<16>(degree, FIND_DEPTH);
    graph.find(0, locator.as_str())
}

#[cfg(feature = "callgrind")]
macro_rules! declare_usize_benches {
    ($runner:ident, { $($name:ident => $degree:expr),+ $(,)? }) => {
        $(
            #[library_benchmark]
            fn $name() -> usize {
                $runner($degree)
            }
        )+
    };
}

#[cfg(feature = "callgrind")]
macro_rules! declare_option_benches {
    ($runner:ident, { $($name:ident => $degree:expr),+ $(,)? }) => {
        $(
            #[library_benchmark]
            fn $name() -> Option<usize> {
                $runner($degree)
            }
        )+
    };
}

#[cfg(feature = "callgrind")]
declare_usize_benches!(
    edge_index_insert_len,
    {
        edge_index_insert_degree_1 => 1,
        edge_index_insert_degree_31 => 31,
        edge_index_insert_degree_32 => 32,
        edge_index_insert_degree_33 => 33,
        edge_index_insert_degree_64 => 64,
    }
);

#[cfg(feature = "callgrind")]
declare_usize_benches!(
    edge_index_remove_count,
    {
        edge_index_remove_degree_1 => 1,
        edge_index_remove_degree_31 => 31,
        edge_index_remove_degree_32 => 32,
        edge_index_remove_degree_33 => 33,
        edge_index_remove_degree_64 => 64,
    }
);

#[cfg(feature = "callgrind")]
declare_usize_benches!(
    edge_index_lookup_count,
    {
        edge_index_lookup_degree_1 => 1,
        edge_index_lookup_degree_31 => 31,
        edge_index_lookup_degree_32 => 32,
        edge_index_lookup_degree_33 => 33,
        edge_index_lookup_degree_64 => 64,
    }
);

#[cfg(feature = "callgrind")]
declare_option_benches!(
    find_locator_hit,
    {
        find_multi_segment_degree_1 => 1,
        find_multi_segment_degree_31 => 31,
        find_multi_segment_degree_32 => 32,
        find_multi_segment_degree_33 => 33,
        find_multi_segment_degree_64 => 64,
    }
);

#[cfg(feature = "callgrind")]
library_benchmark_group!(
    name = edge_index_insert_group;
    benchmarks =
        edge_index_insert_degree_1,
        edge_index_insert_degree_31,
        edge_index_insert_degree_32,
        edge_index_insert_degree_33,
        edge_index_insert_degree_64,
);

#[cfg(feature = "callgrind")]
library_benchmark_group!(
    name = edge_index_remove_group;
    benchmarks =
        edge_index_remove_degree_1,
        edge_index_remove_degree_31,
        edge_index_remove_degree_32,
        edge_index_remove_degree_33,
        edge_index_remove_degree_64,
);

#[cfg(feature = "callgrind")]
library_benchmark_group!(
    name = edge_index_lookup_group;
    benchmarks =
        edge_index_lookup_degree_1,
        edge_index_lookup_degree_31,
        edge_index_lookup_degree_32,
        edge_index_lookup_degree_33,
        edge_index_lookup_degree_64,
);

#[cfg(feature = "callgrind")]
library_benchmark_group!(
    name = find_multi_segment_group;
    benchmarks =
        find_multi_segment_degree_1,
        find_multi_segment_degree_31,
        find_multi_segment_degree_32,
        find_multi_segment_degree_33,
        find_multi_segment_degree_64,
);

#[cfg(feature = "callgrind")]
main!(
    config = LibraryBenchmarkConfig::default();
    library_benchmark_groups =
        edge_index_insert_group,
        edge_index_remove_group,
        edge_index_lookup_group,
        find_multi_segment_group
);

#[cfg(not(feature = "callgrind"))]
fn main() {
    eprintln!(
        "Callgrind benchmarks are disabled. Enable the `callgrind` feature to run benches/edge_index.rs."
    );
}
