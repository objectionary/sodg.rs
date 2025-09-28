// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

//! Criterion benchmarks for `sodg`.
//!
//! Run all benchmarks:
//!   cargo bench --bench bench
//!
//! Run a single benchmark:
//!   cargo bench -- add_vertices
//!
//! Save a baseline and compare:
//!   cargo bench --bench bench -- --save-baseline master
//!   critcmp master branch

#![allow(clippy::unit_arg)]

use std::hint::black_box;
use std::str::FromStr as _;
use std::time::Duration;

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

use sodg::{EdgeIndex, Hex, Label, LabelInterner, Sodg};

mod bench_utils;
use bench_utils::{
    BENCHMARK_DEGREES, build_edge_index, dense_graph_with_locator, label_ids_for_degree,
    populate_edge_index,
};

/// Creates a graph with `n` pre-added vertices.
/// `Sodg::<16>::empty(n)` is used to pre-size the structure to avoid repeated reallocations.
/// This function is used in setup phases (outside the hot path).
fn setup_graph(n: usize) -> Sodg<16> {
    let mut g = Sodg::<16>::empty(n);
    for i in 0..n {
        g.add(i);
    }
    g
}

/// Measures adding N vertices into an empty graph per iteration.
/// We report throughput as `Elements(N)` so `critcmp` can show ops/sec.
fn bench_add_vertices(c: &mut Criterion) {
    let sizes = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("add_vertices");
    for &n in &sizes {
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || Sodg::<16>::empty(n), // setup (not measured)
                |mut g| {
                    // hot path (measured)
                    for i in 0..n {
                        // Measure only the `add` call itself.
                        black_box(g.add(black_box(i)));
                    }
                    black_box(g);
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

/// Measures binding edges along a line with a fixed label.
/// Each iteration starts from a fresh pre-populated graph to keep work per-iter stable.
/// Throughput is the number of successful `bind` calls per iteration.
fn bench_bind_edges(c: &mut Criterion) {
    let sizes = [10, 100, 200];
    let labels = [
        ("alpha", Label::Alpha(0)),
        (
            "long_str",
            Label::from_str("abcdefgh").expect("valid label"),
        ),
    ];
    let mut group = c.benchmark_group("bind_edges");
    for &(name, label) in &labels {
        for &n in &sizes {
            // Approximate number of binds, skipping every 16th edge.
            let ops = if n > 1 { (n - 1) - (n - 1) / 16 } else { 0 };
            group.throughput(Throughput::Elements(ops as u64));
            group.bench_with_input(BenchmarkId::new(name, n), &n, |b, &n| {
                b.iter_batched(
                    || {
                        let mut g = setup_graph(n);
                        let label_id = g.intern_label(&label).expect("intern label");
                        (g, label, label_id)
                    },
                    |(mut g, label, label_id)| {
                        for i in 0..n.saturating_sub(1) {
                            if i % 16 != 0 {
                                // Keep the label interned across binds; erroring here would indicate a test bug.
                                black_box(
                                    g.bind_with_label_id(
                                        black_box(i),
                                        black_box(i + 1),
                                        label_id,
                                        label,
                                    )
                                    .expect("label must remain interned"),
                                );
                            }
                        }
                        black_box(g);
                    },
                    BatchSize::SmallInput,
                );
            });
        }
    }
    group.finish();
}

/// Micro-benchmark for label interner "hit" performance.
/// One iteration does 128 `get` hits and 128 `get_or_intern` hits; we report 256 elements.
fn bench_label_interner_reuse(c: &mut Criterion) {
    let mut group = c.benchmark_group("label_interner_reuse");
    group.throughput(Throughput::Elements(256));
    let labels = [
        ("alpha", Label::Alpha(7)),
        (
            "long_str",
            Label::from_str("abcdefgh").expect("valid label"),
        ),
    ];
    for (name, label) in labels {
        group.bench_function(format!("reuse_{name}"), move |b| {
            b.iter_batched(
                || {
                    let mut interner = LabelInterner::default();
                    interner.get_or_intern(&label).expect("seed intern");
                    interner
                },
                |mut interner| {
                    for _ in 0..128 {
                        black_box(interner.get(&label));
                    }
                    for _ in 0..128 {
                        black_box(interner.get_or_intern(&label).expect("hit intern"));
                    }
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

/// Measures `put` with a fixed payload. We report both elements and, conceptually,
/// bytes-per-iter (commented out) if you want a bytes/sec view in a separate group.
fn bench_put(c: &mut Criterion) {
    let sizes = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("put");
    for &n in &sizes {
        group.throughput(Throughput::Elements(n as u64));
        // If you prefer bytes/sec, uncomment this and create a separate group name:
        // let payload_len = "some string".len();
        // group.throughput(Throughput::Bytes((n * payload_len) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || {
                    let g = setup_graph(n);
                    let payload = Hex::from_str_bytes("some string");
                    (g, payload)
                },
                |(mut g, payload)| {
                    for i in 0..n {
                        black_box(g.put(black_box(i), &payload));
                    }
                    black_box(g);
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

/// Measures `put` immediately followed by `data` lookups on the same keys.
/// Throughput is counted in elements per iteration.
fn bench_put_and_data(c: &mut Criterion) {
    let sizes = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("put_and_data");
    for &n in &sizes {
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || {
                    let g = setup_graph(n);
                    let payload = Hex::from_str_bytes("some string");
                    (g, payload)
                },
                |(mut g, payload)| {
                    for i in 0..n {
                        black_box(g.put(black_box(i), &payload));
                        let _ = black_box(g.data(black_box(i)));
                    }
                    black_box(g);
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

/// Edge-index insertions: measure building an index and inserting `degree` labels per iteration.
/// Throughput is `degree` inserts per iter.
fn bench_edge_index_inserts(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_insert");
    for &degree in &BENCHMARK_DEGREES {
        let labels = label_ids_for_degree(degree);
        group.throughput(Throughput::Elements(labels.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(degree),
            &degree,
            move |b, &_deg| {
                // Setup provides the slice of labels; hot path constructs and populates the index.
                b.iter_batched(
                    || labels.clone(),
                    |labels| {
                        let mut index = EdgeIndex::new();
                        populate_edge_index(&mut index, &labels);
                        black_box(index.len());
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }
    group.finish();
}

/// Edge-index removals: start each iteration from a full index and remove every label.
/// Throughput is `degree` removes per iter.
fn bench_edge_index_removals(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_remove");
    for &degree in &BENCHMARK_DEGREES {
        let labels = label_ids_for_degree(degree);
        group.throughput(Throughput::Elements(labels.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(degree),
            &degree,
            move |b, &_deg| {
                b.iter_batched(
                    || {
                        let mut index = EdgeIndex::new();
                        populate_edge_index(&mut index, &labels);
                        (index, labels.clone())
                    },
                    |(mut index, labels)| {
                        for label in labels {
                            black_box(index.remove(label));
                        }
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }
    group.finish();
}

/// Edge-index lookups: fixed index reused across iterations; lookup each label per iter.
/// Throughput is `degree` lookups per iter.
fn bench_edge_index_lookups(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_lookup");
    for &degree in &BENCHMARK_DEGREES {
        let labels = label_ids_for_degree(degree);
        let index = build_edge_index(&labels);
        group.throughput(Throughput::Elements(labels.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(degree),
            &degree,
            move |b, &_deg| {
                b.iter(|| {
                    for &label in &labels {
                        black_box(index.get(label));
                    }
                });
            },
        );
    }
    group.finish();
}

/// Path search on a dense graph with a fixed depth and degree.
/// Each iteration performs a single `find`; throughput is 1 op/iter.
fn bench_find_multi_segment(c: &mut Criterion) {
    const FIND_DEPTH: usize = 4;
    let mut group = c.benchmark_group("find_multi_segment");
    for &degree in &BENCHMARK_DEGREES {
        let (graph, locator) = dense_graph_with_locator::<16>(degree, FIND_DEPTH);
        group.throughput(Throughput::Elements(1));
        group.bench_with_input(
            BenchmarkId::from_parameter(degree),
            &degree,
            move |b, &_deg| {
                b.iter(|| black_box(graph.find(0, locator.as_str())));
            },
        );
    }
    group.finish();
}

criterion_group!(
    name = benches;
    // Tuning: slightly longer measurement stabilizes ns-scale noise on CI.
    config = Criterion::default()
        .sample_size(30)
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(4));

    targets =
        bench_add_vertices,
        bench_bind_edges,
        bench_put,
        bench_put_and_data,
        bench_edge_index_inserts,
        bench_edge_index_removals,
        bench_edge_index_lookups,
        bench_find_multi_segment,
        bench_label_interner_reuse,
);
criterion_main!(benches);
