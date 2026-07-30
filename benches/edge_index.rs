// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

//! Benchmarks of the per-vertex edge index around the point where it stops
//! being flat and turns into a hash map.
//!
//! The graph is `Sodg<16>`, the configuration every test in this repository
//! and the `reo` project use, so the transition measured here is the one that
//! actually happens in production: the sixteenth edge of a vertex is the last
//! one the flat shape holds, and the seventeenth turns the index into a hash
//! map.
//!
//! Reaching those degrees does not need a wide graph. `MAX_BRANCH_SIZE` bounds
//! how many vertices a branch holds, not how many edges leave a vertex, and
//! several labels may point at the same target, so a vertex of any degree is
//! built out of two vertices. That is what [`star`] does.

use std::hint::black_box;
use std::time::Duration;

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use sodg::{Label, Sodg};

/// The threshold this crate is used with everywhere.
const FLAT: usize = 16;

/// Degrees on either side of the transition.
///
/// Sixteen is the last flat degree and seventeen the first hashed one, so that
/// pair prices the transition itself; the rest bracket it, up to the
/// sixty-four the originating issue asks for.
const DEGREES: [usize; 7] = [1, 8, 15, 16, 17, 32, 64];

/// A label that [`star`] interns without binding it to vertex zero.
const ABSENT: Label = Label::Greek('ω');

/// Make a graph of two vertices where vertex zero has no edges.
fn bare() -> Sodg<FLAT> {
    let mut graph = Sodg::<FLAT>::empty(4);
    graph.add(0);
    graph.add(1);
    graph
}

/// Make a graph where the given number of distinct labels depart from vertex
/// zero, all of them pointing at vertex one.
///
/// Vertex one also gets an edge labelled [`ABSENT`] back to vertex zero, so
/// that the graph has interned that label while keeping it out of the index of
/// vertex zero. Without it, looking [`ABSENT`] up on vertex zero would stop at
/// the interner and never reach the index, which is the one thing the
/// missing-lookup group exists to measure.
fn star(degree: usize) -> Sodg<FLAT> {
    let mut graph = bare();
    for i in 1..=degree {
        graph.bind(0, 1, Label::Alpha(i));
    }
    graph.bind(1, 0, ABSENT);
    graph
}

/// How many elements one iteration of a group covers.
fn elements(degree: usize) -> Throughput {
    Throughput::Elements(u64::try_from(degree).unwrap())
}

/// Look up every edge of vertex zero, one by one.
fn bench_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_lookup");
    for &degree in &DEGREES {
        let graph = star(degree);
        group.throughput(elements(degree));
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

/// Look up a label the graph knows but vertex zero does not have.
fn bench_missing_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_lookup_missing");
    for &degree in &DEGREES {
        let graph = star(degree);
        group.throughput(elements(1));
        group.bench_with_input(BenchmarkId::from_parameter(degree), &degree, |b, _| {
            b.iter(|| {
                black_box(graph.kid(black_box(0), black_box(ABSENT)));
            });
        });
    }
    group.finish();
}

/// Bind every edge of a star whose vertices already exist.
fn bench_bind(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_bind");
    for &degree in &DEGREES {
        group.throughput(elements(degree));
        group.bench_with_input(
            BenchmarkId::from_parameter(degree),
            &degree,
            |b, &degree| {
                b.iter_batched(
                    bare,
                    |mut graph| {
                        for i in 1..=degree {
                            graph.bind(black_box(0), black_box(1), black_box(Label::Alpha(i)));
                        }
                        graph
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }
    group.finish();
}

/// Walk every edge of vertex zero.
fn bench_kids(c: &mut Criterion) {
    let mut group = c.benchmark_group("edge_index_kids");
    for &degree in &DEGREES {
        let graph = star(degree);
        group.throughput(elements(degree));
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

/// Keep the whole suite well inside the fifteen minutes the `cargo` workflow
/// allows for two test runs, a doc build, clippy and both bench targets.
///
/// Four seconds per benchmark over twenty-eight of them is under two minutes,
/// which is less than the four groups cost before, when they measured five
/// degrees each at the default five-second measurement. The effects being
/// measured are tens of nanoseconds apart, so they survive the shorter window.
fn config() -> Criterion {
    Criterion::default()
        .sample_size(20)
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(3))
}

criterion_group!(
    name = benches;
    config = config();
    targets = bench_lookup, bench_missing_lookup, bench_bind, bench_kids,
);
criterion_main!(benches);
