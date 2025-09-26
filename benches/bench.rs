// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

#![allow(clippy::unit_arg)]
/// Benchmark Usage:
///
/// `cargo bench --bench bench` will run all Criterion benchmarks in this file.
/// ("--bench bench" for this file named "bench.rs", without this, the command
/// `cargo bench` will run all benchmarks in the project.)
///
/// Individual benchmarks can be executed with
/// `cargo bench -- bench_name`, for example `cargo bench -- add_vertices`.
/// To profile the edge index with Callgrind, enable the `callgrind` feature
/// and run `cargo bench --features callgrind --bench edge_index`.
use std::hint::black_box;

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};

use sodg::{EdgeIndex, Hex, Label, Sodg};

mod bench_utils;

use bench_utils::{
    BENCHMARK_DEGREES, build_edge_index, dense_graph_with_locator, label_ids_for_degree,
    populate_edge_index,
};

fn setup_graph(n: usize) -> Sodg<16> {
    let mut graph = Sodg::<16>::empty(n);
    for i in 0..n {
        graph.add(i);
    }
    graph
}

fn bench_add_vertices(c: &mut Criterion) {
    let sizes = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("add_vertices");
    for &size in &sizes {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            let mut graph = black_box(Sodg::<16>::empty(black_box(size)));
            b.iter(|| {
                for i in 0..size {
                    black_box(graph.add(black_box(i)));
                }
                black_box(&mut graph);
            });
        });
    }
    group.finish();
}

fn bench_bind_edges(c: &mut Criterion) {
    let sizes = [10, 100, 200];
    let mut group = c.benchmark_group("bind_edges");
    for &size in &sizes {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            let mut graph = setup_graph(size);
            b.iter(|| {
                for i in 0..size - 1 {
                    if i % 16 != 0 {
                        black_box(graph.bind(
                            black_box(i),
                            black_box(i + 1),
                            black_box(Label::Alpha(0)),
                        ));
                    }
                }
                black_box(&mut graph);
            });
        });
    }
    group.finish();
}

fn bench_put(c: &mut Criterion) {
    let sizes = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("put");
    for &size in &sizes {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            let mut graph = setup_graph(size);
            b.iter(|| {
                for i in 0..size {
                    black_box(
                        graph.put(black_box(i), black_box(&Hex::from_str_bytes("some string"))),
                    );
                }
                black_box(&mut graph);
            });
        });
    }
    group.finish();
}

fn bench_put_and_data(c: &mut Criterion) {
    let sizes = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("put_and_data");
    for &size in &sizes {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            let mut graph = setup_graph(size);
            b.iter(|| {
                for i in 0..size {
                    black_box(
                        graph.put(black_box(i), black_box(&Hex::from_str_bytes("some string"))),
                    );
                    _ = black_box(graph.data(black_box(i)));
                }
                black_box(&mut graph);
            });
        });
    }
    group.finish();
}

fn bench_edge_index_inserts(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_insert");
    for &degree in &BENCHMARK_DEGREES {
        let labels = label_ids_for_degree(degree);
        group.bench_with_input(
            BenchmarkId::from_parameter(degree),
            &degree,
            move |b, &_deg| {
                b.iter(|| {
                    let mut index = EdgeIndex::new();
                    populate_edge_index(&mut index, &labels);
                    black_box(index.len());
                });
            },
        );
    }
    group.finish();
}

fn bench_edge_index_removals(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_remove");
    for &degree in &BENCHMARK_DEGREES {
        let labels = label_ids_for_degree(degree);
        group.bench_with_input(
            BenchmarkId::from_parameter(degree),
            &degree,
            move |b, &_deg| {
                b.iter_batched(
                    || {
                        let mut index = EdgeIndex::new();
                        populate_edge_index(&mut index, &labels);
                        index
                    },
                    |mut index| {
                        for &label in &labels {
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

fn bench_edge_index_lookups(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_lookup");
    for &degree in &BENCHMARK_DEGREES {
        let labels = label_ids_for_degree(degree);
        let index = build_edge_index(&labels);
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

fn bench_find_multi_segment(c: &mut Criterion) {
    const FIND_DEPTH: usize = 4;
    let mut group = c.benchmark_group("find_multi_segment");
    for &degree in &BENCHMARK_DEGREES {
        let (graph, locator) = dense_graph_with_locator::<16>(degree, FIND_DEPTH);
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
    config = Criterion::default().sample_size(20);
    targets =
        bench_add_vertices,
        bench_bind_edges,
        bench_put,
        bench_put_and_data,
        bench_edge_index_inserts,
        bench_edge_index_removals,
        bench_edge_index_lookups,
        bench_find_multi_segment,
);
criterion_main!(benches);
