// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::time::{Duration, Instant};

use sodg::{Hex, Label, Sodg};

trait Book {
    fn price(&self) -> i64;
}

struct Prime {
    usd: i64,
}

impl Book for Prime {
    fn price(&self) -> i64 {
        self.usd
    }
}

struct Discounted {
    book: Box<dyn Book>,
}

impl Book for Discounted {
    fn price(&self) -> i64 {
        self.book.price() / 2
    }
}

#[allow(clippy::missing_panics_doc)]
#[must_use]
pub fn on_graph(total: usize) -> (i64, Duration) {
    let mut g: Sodg<16> = Sodg::empty(total * 4);
    g.add(0);
    let mut sum = 0;
    let start = Instant::now();
    let forty_two = Hex::from(42);
    for _ in 0..total {
        let v1 = 1;
        g.add(v1);
        let v2 = v1 + 1;
        g.add(v2);
        g.bind(v1, v2, Label::Alpha(0)).unwrap();
        g.bind(v2, v1, Label::Greek('ρ')).unwrap();
        let v3 = v2 + 1;
        g.add(v3);
        g.bind(v2, v3, Label::Greek('Δ')).unwrap();
        g.put(v3, &forty_two);
        let v4 = v3 + 1;
        g.add(v4);
        g.bind(v4, v1, Label::Greek('φ')).unwrap();
        assert!(g.kid(v4, Label::Alpha(0)).is_none());
        g.kid(v4, Label::Greek('φ')).unwrap();
        g.kid(v1, Label::Alpha(0)).unwrap();
        let k = g.kid(v2, Label::Greek('Δ')).unwrap();
        sum += g.data(k).unwrap().to_i64().unwrap() / 2;
    }
    (std::hint::black_box(sum), start.elapsed())
}

#[must_use]
pub fn on_heap(total: usize) -> (i64, Duration) {
    let mut sum = 0;
    let start = Instant::now();
    for _ in 0..total {
        let prime = std::hint::black_box(Box::new(Prime { usd: 42 }));
        let discounted = std::hint::black_box(Box::new(Discounted { book: prime }));
        sum += discounted.price();
    }
    (std::hint::black_box(sum), start.elapsed())
}

#[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss, clippy::cast_sign_loss)]
fn u128_to_f64(x: u128) -> Option<f64> {
    let res = x as f64;
    (res as u128 == x).then_some(res)
}

fn main() {
    let total = 1_000_000;
    let (s1, d1) = on_graph(total);
    println!("on_graph: {d1:?}");
    let (s2, d2) = on_heap(total);
    let d1_nanos = u128_to_f64(d1.as_nanos()).unwrap();
    let d2_nanos = u128_to_f64(d2.as_nanos()).unwrap();
    println!("on_heap: {d2_nanos:?}");
    println!("gain: {:.2}x", d2_nanos / d1_nanos);
    println!("loss: {:.2}x", d1_nanos / d2_nanos);
    assert_eq!(s1, s2);
}
