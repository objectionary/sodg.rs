// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

//! Benchmarks of the per-vertex edge index around the point where it stops
//! being flat and turns into a hash map.
//!
//! The graph is parametrised by `FLAT`, the number of edges the flat shape
//! holds. Degrees below it stay flat, degrees above it are hashed, so the
//! pairs 31/33 and 32/33 show the price of the transition.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use sodg::{Label, Sodg};

/// How many edges the flat shape of the index holds.
///
/// It is deliberately small, because a branch of the graph holds at most
/// `MAX_BRANCH_SIZE` vertices, which puts a star of a much higher degree out
/// of reach of the public API.
const FLAT: usize = 4;

/// Degrees around the flat-to-hashed transition.
const DEGREES: [usize; 5] = [1, 3, 4, 5, 12];

/// Make a graph where vertex zero has the given number of departing edges.
fn star(degree: usize) -> Sodg<FLAT> {
    let mut graph = Sodg::<FLAT>::empty(degree + 2);
    graph.add(0);
    for i in 1..=degree {
        graph.add(i);
        graph.bind(0, i, Label::Alpha(i));
    }
    graph
}

fn bench_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_lookup");
    for &degree in &DEGREES {
        let graph = star(degree);
        group.throughput(Throughput::Elements(degree as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(degree),
            &degree,
            |b, &degree| {
                b.iter(|| {
                    for i in 1..=degree {
                        black_box(graph.kid(black_box(0), black_box(Label::Alpha(i))));
                    }
                });
            },
        );
    }
    group.finish();
}

fn bench_missing_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_lookup_missing");
    for &degree in &DEGREES {
        let graph = star(degree);
        group.throughput(Throughput::Elements(1));
        group.bench_with_input(BenchmarkId::from_parameter(degree), &degree, |b, _| {
            b.iter(|| {
                black_box(graph.kid(black_box(0), black_box(Label::Greek('ω'))));
            });
        });
    }
    group.finish();
}

fn bench_bind(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_bind");
    for &degree in &DEGREES {
        group.throughput(Throughput::Elements(degree as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(degree),
            &degree,
            |b, &degree| {
                b.iter(|| {
                    black_box(star(black_box(degree)));
                });
            },
        );
    }
    group.finish();
}

fn bench_kids(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_kids");
    for &degree in &DEGREES {
        let graph = star(degree);
        group.throughput(Throughput::Elements(degree as u64));
        group.bench_with_input(BenchmarkId::from_parameter(degree), &degree, |b, _| {
            b.iter(|| {
                for kid in graph.kids(black_box(0)) {
                    black_box(kid);
                }
            });
        });
    }
    group.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default().sample_size(20);
    targets = bench_lookup, bench_missing_lookup, bench_bind, bench_kids,
);
criterion_main!(benches);
