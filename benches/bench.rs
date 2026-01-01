// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

#![allow(clippy::unit_arg)]
/// Benchmark Usage:
///
/// `cargo bench --bench bench` will run all benchmarks in this file.
/// ("--bench bench" for this file named "bench.rs", without this, the
/// command `cargo bench` will run all benchmarks in the project.)
///
/// If you want to run a single benchmark, you can use the command
/// `cargo bench -- bench_name`, for example `cargo bench -- add_vertices`.
use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

use sodg::{Hex, Label, Sodg};

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

criterion_group!(
    name = benches;
    config = Criterion::default().sample_size(20);
    targets = bench_add_vertices, bench_bind_edges, bench_put, bench_put_and_data,
);
criterion_main!(benches);
