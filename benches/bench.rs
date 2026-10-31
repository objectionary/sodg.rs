// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

#![allow(clippy::unit_arg)]

use std::hint::black_box;

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use sodg::{Hex, Label, Sodg};

/// Build a graph sized for `n` and pre-filled with vertex IDs `[0, n)`.
/// Pre-sizing avoids extra reallocations during bench hot paths.
fn setup_graph(n: usize) -> Sodg<16> {
    let mut g = Sodg::<16>::empty(n);
    for i in 0..n {
        g.add(i);
    }
    g
}

/// Benchmark: insert `n` vertices into a fresh empty graph per iteration.
/// Throughput is the number of vertices inserted (`Elements(n)`).
fn bench_add_vertices(c: &mut Criterion) {
    let sizes = [10_usize, 100, 1000, 10_000];
    let mut group = c.benchmark_group("add_vertices");
    for &n in &sizes {
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || Sodg::<16>::empty(n),
                |mut g| {
                    for i in 0..n {
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

/// Benchmark: for a fresh graph with `n` vertices, bind edges in a line,
/// skipping each 16th edge to emulate sparsity. Throughput equals the
/// actual number of `bind` operations performed.
fn bench_bind_edges(c: &mut Criterion) {
    let sizes = [10_usize, 100, 200];
    let mut group = c.benchmark_group("bind_edges");
    for &n in &sizes {
        let edges = n.saturating_sub(1);
        let skipped = edges / 16;
        let ops = edges.saturating_sub(skipped);
        group.throughput(Throughput::Elements(ops as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || setup_graph(n),
                |mut g| {
                    let label = Label::Alpha(0);
                    for i in 0..n.saturating_sub(1) {
                        if i % 16 != 0 {
                            black_box(g.bind(black_box(i), black_box(i + 1), label));
                        }
                    }
                    black_box(g);
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

/// Benchmark: write a fixed payload for `n` keys into a fresh graph per iteration.
/// Payload is prepared in setup. Throughput is `Elements(n)`.
fn bench_put(c: &mut Criterion) {
    let sizes = [10_usize, 100, 1000, 10_000];
    let mut group = c.benchmark_group("put");
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
                        black_box(g.put(black_box(i), black_box(&payload)));
                    }
                    black_box(g);
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

/// Benchmark: for each key, `put` the payload then fetch `data`.
/// Throughput is `Elements(n)`.
fn bench_put_and_data(c: &mut Criterion) {
    let sizes = [10_usize, 100, 1000, 10_000];
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
                        black_box(g.put(black_box(i), black_box(&payload)));
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

criterion_group!(
    name = benches;
    config = Criterion::default().sample_size(30);
    targets = bench_add_vertices, bench_bind_edges, bench_put, bench_put_and_data,
);
criterion_main!(benches);
