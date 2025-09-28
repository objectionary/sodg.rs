// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

#![allow(clippy::unit_arg)]

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};
use sodg::{Hex, Label, Sodg};

/// Build a graph pre-sized to `n` and pre-filled with vertex IDs [0, n).
/// Sizing up-front avoids repeated reallocations in benchmarks.
fn setup_graph(n: usize) -> Sodg<16> {
    let mut g = Sodg::<16>::empty(n);
    for i in 0..n {
        g.add(i);
    }
    g
}

/// add_vertices: insert N vertices into an empty graph per iteration.
/// Setup happens outside the hot path; throughput is `Elements(N)`.
fn bench_add_vertices(c: &mut Criterion) {
    let sizes: [usize; 4] = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("add_vertices");

    for &n in &sizes {
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || Sodg::<16>::empty(n), // setup (not measured)
                |mut g| {
                    // hot path (measured)
                    for i in 0..n {
                        black_box(g.add(black_box(i)));
                    }
                    black_box(g); // keep value alive
                },
                BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

/// bind_edges: each iteration starts from a fresh graph with N vertices.
/// Bind edges in a line while skipping every 16th to emulate sparsity.
/// Throughput equals the actual number of bind operations performed.
fn bench_bind_edges(c: &mut Criterion) {
    let sizes: [usize; 3] = [10, 100, 200];
    let mut group = c.benchmark_group("bind_edges");

    for &n in &sizes {
        let edges = n.saturating_sub(1);
        let skipped = edges / 16;
        let ops = edges.saturating_sub(skipped);
        group.throughput(Throughput::Elements(ops as u64));

        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || setup_graph(n), // setup (not measured)
                |mut g| {
                    // hot path (measured)
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

/// put: write a fixed payload for N keys into a fresh graph per iteration.
/// Payload is prepared once in setup; throughput is `Elements(N)`.
fn bench_put(c: &mut Criterion) {
    let sizes: [usize; 4] = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("put");

    for &n in &sizes {
        group.throughput(Throughput::Elements(n as u64));

        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || {
                    let g = setup_graph(n);
                    let payload = Hex::from_str_bytes("some string");
                    (g, payload)
                }, // setup (not measured)
                |(mut g, payload)| {
                    // hot path (measured)
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

/// put_and_data: for each key, put payload and then fetch data.
/// Throughput is `Elements(N)`. Only the hot path is measured.
fn bench_put_and_data(c: &mut Criterion) {
    let sizes: [usize; 4] = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("put_and_data");

    for &n in &sizes {
        group.throughput(Throughput::Elements(n as u64));

        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || {
                    let g = setup_graph(n);
                    let payload = Hex::from_str_bytes("some string");
                    (g, payload)
                }, // setup (not measured)
                |(mut g, payload)| {
                    // hot path (measured)
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
    // Keep the run time reasonable while reducing ns-scale noise.
    config = Criterion::default().sample_size(30);
    targets = bench_add_vertices, bench_bind_edges, bench_put, bench_put_and_data,
);
criterion_main!(benches);

