# Surging Object Di-Graph, in Rust

[![EO principles respected here](https://www.elegantobjects.org/badge.svg)](https://www.elegantobjects.org)
[![We recommend IntelliJ IDEA](https://www.elegantobjects.org/intellij-idea.svg)](https://www.jetbrains.com/idea/)

[![cargo](https://github.com/objectionary/sodg/actions/workflows/cargo.yml/badge.svg)](https://github.com/objectionary/sodg/actions/workflows/cargo.yml)
[![crates.io](https://img.shields.io/crates/v/sodg.svg)](https://crates.io/crates/sodg)
[![PDD status](https://www.0pdd.com/svg?name=objectionary/sodg)](https://www.0pdd.com/p?name=objectionary/sodg)
[![codecov](https://codecov.io/gh/objectionary/sodg/branch/master/graph/badge.svg)](https://codecov.io/gh/objectionary/sodg)
[![Hits-of-Code](https://hitsofcode.com/github/objectionary/sodg)](https://hitsofcode.com/view/github/objectionary/sodg)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](https://github.com/objectionary/sodg/blob/master/LICENSE.txt)
[![docs.rs](https://img.shields.io/docsrs/sodg)](https://docs.rs/sodg/latest/sodg/)

This Rust library implements a Surging Object DiGraph (SODG) for
[reo](https://github.com/objectionary/reo) virtual machine for
[EO](https://www.eolang.org) programs. The graph is "surging" because
it automatically behind the scene deletes vertices and edges from itself,
which is also known as "garbage collection" mechanism. A vertex gets deleted
right after the data it contains is read _and_ no other vertices
transitively point to it.

The current implementation keeps runtime overhead low by interning edge labels
and indexing them through a hybrid small-map/hash-map structure. Edge payloads
are stored in a `Hex` helper that keeps tiny blobs inline and promotes larger
values to reference-counted slices so cloning a graph snapshot stays cheap.

Here is how you can create a di-graph:

```rust
use std::str::FromStr as _;
use sodg::{Hex, Label, Sodg};
let mut g: Sodg<16> = Sodg::empty(256);
g.add(0); // add a vertex no.0
g.add(1); // add a vertex no.1
g.bind(0, 1, Label::from_str("foo").unwrap()).unwrap(); // connect v0 to v1 with label "foo"
g.bind(0, 1, Label::from_str("bar").unwrap()).unwrap(); // add another edge with label "bar"
g.put(1, &Hex::from_str_bytes("Hello, world!")); // attach data to v1
```

Then, you can find a vertex by the label of an edge departing
from another vertex:

```rust
let id = g.kid(0, Label::from_str("foo").unwrap()).unwrap();
assert_eq!(1, id);
```

Then, you can find all kids of a vertex:

```rust
let mut kids = g.kids(0);
let first = kids.next().unwrap();
assert_eq!("foo", first.label().to_string());
assert_eq!(1, first.destination());
let second = kids.next().unwrap();
assert_eq!("bar", second.label().to_string());
let label_id = first.label_id();
assert!(label_id > 0);
```

Then, you can read the data of a vertex:

```rust
let hex: Hex = g.data(1);
let num: i64 = hex.to_i64()?;
assert_eq!(42, num);
```

Then, you can print the graph:

```rust
println!("{:?}", g);
```

Multi-hop traversals remain ergonomic thanks to [`Sodg::find`], which walks a
dot-separated path and returns the final vertex if each edge exists:

```rust
assert_eq!(Some(1), g.find(0, "foo"));
assert_eq!(None, g.find(0, "foo.baz"));
```

Using `merge()`, you can merge two graphs together, provided they are trees.

Using `save()` and `load()`, you can serialize and deserialize the graph.

Using `to_xml()` and `to_dot()`, you can print it to
[XML](https://en.wikipedia.org/wiki/XML) and
[DOT](https://graphviz.org/doc/info/lang.html).

Using `slice()` and `slice_some()`, you can take a part/slice
of the graph (mostly for debugging purposes).

Read [the documentation](https://docs.rs/sodg/latest/sodg/).

## Benchmarks

The project ships two complementary benchmarking harnesses:

* A [Criterion](https://github.com/bheisler/criterion.rs) suite in
  `benches/bench.rs` that measures wall-clock performance of vertex management,
  edge insertion/removal/lookups, and multi-segment `find()` traversals across
  different out-degrees.
* An [`iai-callgrind`](https://github.com/gungraun/gungraun) harness in
  `benches/edge_index.rs` (guarded by the `callgrind` feature) that collects
  Valgrind statistics for the same scenarios.

Criterion only requires a stable Rust toolchain. Gnuplot is optional; when it is
not installed, Criterion falls back to the bundled Plotters backend for report
generation.

### Running Criterion locally

1. Build and run all Criterion benchmarks:
   ```bash
   cargo bench --bench bench
   ```
2. Inspect the generated reports under
   `target/criterion/<benchmark>/<measurement>/report/index.html`. They include
   plots, summary statistics, and raw sample data.

### Comparing against a saved baseline

Criterion can persist previous results to highlight regressions and
improvements:

1. Check out the branch or commit that should become the reference point (for
   example `master`) and save a baseline:
   ```bash
   cargo bench --bench bench -- --save-baseline master
   ```
   The snapshot is stored inside `target/criterion` and can be reused across
   branches as long as the directory is kept intact.
2. Switch back to your working branch and compare the current code against the
   saved numbers:
   ```bash
   cargo bench --bench bench -- --baseline master
   ```
3. Examine the console output or open the HTML reports to see per-benchmark
   percentage changes. Positive percentages indicate improvements, negative ones
   signal regressions.

To focus on a single benchmark group, pass its name after a double dash, e.g.
`cargo bench --bench bench -- find_multi_segment`.

### Running the Callgrind harness

The Callgrind harness provides instruction- and cache-level metrics:

1. Install Valgrind (`apt install valgrind` on Debian/Ubuntu). Gungraun supports
   Linux and other platforms with working Valgrind ports; Windows is not
   supported.
2. Enable the `callgrind` feature and execute the harness:
   ```bash
   cargo bench --features callgrind --bench edge_index
   ```
3. Review the generated profiles under `target/iai` with tools like
   `kcachegrind`, `callgrind_annotate`, or Gungraun’s HTML report. This makes it
   easy to inspect hot paths and validate that optimizations change instruction
   counts in the intended way.

When the feature is not enabled, the `edge_index` binary prints a short message
and exits immediately so the harness can stay in the repository without adding a
hard dependency on Valgrind.

## How to Contribute

First, install [Rust](https://www.rust-lang.org/tools/install) and then:

```bash
cargo test -vv
```

If everything goes well, fork repository, make changes, send us a
[pull request](https://www.yegor256.com/2014/04/15/github-guidelines.html).
We will review your changes and apply them to the `master` branch shortly,
provided they don't violate our quality standards. To avoid frustration,
before sending us your pull request please run `cargo test` again. Also,
run `cargo fmt` and `cargo clippy`.
