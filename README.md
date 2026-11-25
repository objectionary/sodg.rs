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
[EO](https://www.eolang.org) programs. Cells are never deleted:
once made, a cell stays in the graph, and reading its data
doesn't change anything, so an object may be dataized
any number of times.

Each cell of the graph stands for a 𝜑-expression.
There are seven methods that build the graph, one per command
printed by [`phino sodg`](https://github.com/objectionary/phino):

| Command | Method | What it does |
| --- | --- | --- |
| `F o attr0 attr1 ...` | `formation()` | makes `o` a formation |
| `D o base attr` | `dispatch()` | makes `o` the dispatch `base.attr` |
| `A o proto attr arg` | `application()` | makes `o` the `proto( attr ↦ arg )` |
| `T o` | `termination()` | makes `o` the termination `⊥` |
| `P o attr kid` | `put()` | puts `kid` to the attribute `attr` of `o` |
| `Δ o data` | `delta()` | sets the Δ-asset of `o` |
| `λ o name` | `lambda()` | sets the λ-asset of `o` |

A dispatch cell has a single edge `π` to its base and keeps the
attribute in its `Kind::Dispatch`.
An application cell has an edge `π` to its proto, an edge `attr`
to its argument, and keeps the attribute in its `Kind::Application`.

Here is how you can create a graph:

```rust
use std::str::FromStr as _;
use sodg::{Hex, Label, Sodg};
let mut g: Sodg<16> = Sodg::empty(256);
let x = Label::from_str("x").unwrap();
g.formation(0, &[x]); // make a formation ⟦ x ↦ ? ⟧ in cell no.0
g.formation(1, &[]); // make an empty formation in cell no.1
g.delta(1, &Hex::from(42_i64)); // attach data to cell no.1
g.put(0, x, 1); // put cell no.1 to the attribute "x" of cell no.0
g.dispatch(2, 0, x); // make cell no.2 for the dispatch of "x" from cell no.0
g.lambda(0, "L_foo"); // set the λ-asset of cell no.0
```

The same graph can be deployed from the output of `phino sodg`:

```rust
use sodg::Script;
Script::from_str(
  "F c0 x\nF c1\nΔ c1 00-00-00-00-00-00-00-2A\nP c0 x c1\nD c2 c0 x\nλ c0 L_foo"
).deploy_to(&mut g)?;
```

Then, you can find a cell by the label of an edge departing
from another cell:

```rust
let id = g.kid(0, x).unwrap();
assert_eq!(1, id);
```

Then, you can find all kids of a cell:

```rust
let kids: Vec<(&Label, &usize)> = g.kids(0).collect();
assert_eq!("x", kids[0].0.to_string());
assert_eq!(1, *kids[0].1);
```

Then, you can read the data of a cell:

```rust
let hex: Hex = g.data(1).unwrap();
let num: i64 = hex.to_i64()?;
assert_eq!(42, num);
```

Then, you can print the graph:

```rust
println!("{:?}", g);
```

Using `merge()`, you can merge two graphs together, provided they are trees.

Using `save()` and `load()`, you can serialize and deserialize the graph.

Using `to_xml()` and `to_dot()`, you can print it to
[XML](https://en.wikipedia.org/wiki/XML) and
[DOT](https://graphviz.org/doc/info/lang.html).

Using `slice()` and `slice_some()`, you can take a part/slice
of the graph (mostly for debugging purposes).

Read [the documentation](https://docs.rs/sodg/latest/sodg/).

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
