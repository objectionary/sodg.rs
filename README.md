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
g.bind(0, 1, Label::from_str("foo").unwrap()); // connect v0 to v1 with label "foo"
g.bind(0, 1, Label::from_str("bar").unwrap()); // add another edge with label "bar"
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

Criterion benchmarks live under `benches/bench.rs` and cover vertex management,
edge insertion/removal/lookups, and multi-segment `find()` traversals across
degrees 1, 31, 32, 33, and 64. The label interner and hybrid edge index keep the
hot path allocation-free for vertices with a small fan-out and continue to scale
once a vertex surpasses 32 distinct edges. Run all Criterion suites with:

```bash
cargo bench --bench bench
```

Individual benches can be executed with `cargo bench -- bench_name`, for
example `cargo bench -- edge_index_insert`.

The repository also ships an [`iai-callgrind`](https://github.com/iai-callgrind/iai-callgrind)
harness in `benches/edge_index.rs` that records the same scenarios under
Callgrind. Install Valgrind locally, enable the `callgrind` feature, and run:

```bash
cargo bench --features callgrind --bench edge_index
```

When the feature is not enabled, the binary prints a short message and exits so
it can be kept in regular workflows without requiring Callgrind.

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
