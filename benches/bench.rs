// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

#![allow(clippy::unit_arg)]

use std::hint::black_box;

use criterion::{
    BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main,
};
use sodg::{Hex, Label, Sodg};

fn setup_graph(n: usize) -> Sodg<16> {
    let mut g = Sodg::<16>::empty(n);
    for i in 0..n {
        g.add(i);
    }
    g
}

// add_vertices: меряем только добавление N вершин в ПУСТОЙ граф на каждую итерацию
// (setup графа вне измеряемой части).
fn bench_add_vertices(c: &mut Criterion) {
    let sizes = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("add_vertices");
    for &n in &sizes {
        group.throughput(Throughput::Elements(n as u64)); // tell Criterion items/iter
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || Sodg::<16>::empty(n),            // setup (not measured)
                |mut g| {                           // hot path (measured)
                    for i in 0..n {
                        // measure add only, avoid extra work
                        black_box(g.add(black_box(i)));
                    }
                    black_box(g); // keep it alive
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

// bind_edges: каждый прогон стартует со свежего графа из N вершин.
// Внутри итерации только .bind().
fn bench_bind_edges(c: &mut Criterion) {
    let sizes = [10, 100, 200];
    let mut group = c.benchmark_group("bind_edges");
    for &n in &sizes {
        // Кол-во операций ~ (n - n/16 - 1); для простоты репортим n как верхнюю оценку
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || setup_graph(n),
                |mut g| {
                    for i in 0..n - 1 {
                        if i % 16 != 0 {
                            black_box(g.bind(
                                black_box(i),
                                black_box(i + 1),
                                black_box(Label::Alpha(0)),
                            ));
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

// put: фиксируем payload один раз в setup, внутри итерации только .put().
fn bench_put(c: &mut Criterion) {
    let sizes = [10, 100, 1000, 10_000];
    let mut group = c.benchmark_group("put");

    // Можно также репортить Throughput::Bytes(bytes_per_iter), если хочешь байтовую пропускную способность:
    // let bytes_per_item = "some string".len(); // 11
    // group.throughput(Throughput::Bytes((n * bytes_per_item) as u64));

    for &n in &sizes {
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_batched(
                || {
                    let g = setup_graph(n);
                    // precompute payload once
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

// put_and_data: аналогично, .put() + .data() в горячей секции, всё остальное снаружи.
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
                        black_box(g.put(black_box(i), black_box(&payload)));
                        // Only measure the lookup, don't format/clone results
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
    // Немного стабильнее на мелких «ns»-тестах:
    // .sample_size(40) уменьшит шум, но увеличит время; подбери под железо CI.
    config = Criterion::default().sample_size(30);
    targets = bench_add_vertices, bench_bind_edges, bench_put, bench_put_and_data,
);
criterion_main!(benches);

