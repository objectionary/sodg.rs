// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

//! This is a memory structure with cells and edges between them,
//! which we call Surging Object `DiGraph` (SODG), because it expects
//! modifications coming from a user (through [`Sodg::formation`],
//! [`Sodg::dispatch`], [`Sodg::application`], [`Sodg::put`],
//! [`Sodg::delta`], and [`Sodg::lambda`]) and then decides itself when
//! it's time to delete some cells (something similar to
//! "garbage collection").
//!
//! Every cell stands for a 𝜑-expression and has a [`Kind`]:
//!
//! - `F o attr0 attr1 ...` makes the cell `o` a formation with these
//!   attributes, see [`Sodg::formation`]. The attributes are kept in the
//!   cell, see [`Sodg::attrs`], while their values are attached later
//!   by `P`.
//! - `D o base attr` makes the cell `o` the dispatch `base.attr`,
//!   see [`Sodg::dispatch`]. The cell gets the kind [`Kind::Dispatch`]
//!   with `attr` inside and a single edge `π` pointing to `base`.
//!   The dispatch is not resolved while the graph is being built.
//! - `A o proto attr arg` makes the cell `o` the application
//!   `proto( attr ↦ arg )`, see [`Sodg::application`]. The cell gets the
//!   kind [`Kind::Application`] with `attr` inside, an edge `π` pointing
//!   to `proto`, and an edge `attr` pointing to `arg`.
//! - `P o attr kid` puts `kid` to the attribute `attr` of `o`, making
//!   an edge `attr` from `o` to `kid`, see [`Sodg::put`].
//! - `Δ o data` sets the Δ-asset of `o`, see [`Sodg::delta`].
//! - `λ o name` sets the λ-asset of `o`, see [`Sodg::lambda`].
//!
//! For example, here is how you create a formation with a single
//! attribute `foo`, which is bound to another formation:
//!
//! ```
//! use std::str::FromStr as _;
//!
//! use sodg::{Label, Sodg};
//! let mut sodg: Sodg<16> = Sodg::empty(256);
//! let foo = Label::from_str("foo").unwrap();
//! sodg.formation(0, &[foo]);
//! sodg.formation(1, &[]);
//! sodg.put(0, foo, 1);
//! assert_eq!(1, sodg.kid(0, foo).unwrap());
//! ```

#![doc(html_root_url = "https://docs.rs/sodg/0.0.0")]
#![deny(warnings)]
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
#![allow(clippy::multiple_inherent_impl)]
#![allow(clippy::multiple_crate_versions)]

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

mod clone;
mod ctors;
mod debug;
mod dot;
mod find;
mod hex;
mod inspect;
mod label;
mod merge;
mod misc;
mod next;
mod ops;
mod script;
mod serialization;
mod slice;
mod xml;

const HEX_SIZE: usize = 8;
// @todo #313:90min A branch can't hold more than `MAX_BRANCH_SIZE` cells,
//  while the output of `phino sodg` for any real program has many more
//  cells connected to each other. Deploying such an output with
//  `Script::deploy_to()` panics with "No more space left in the stack" from
//  `microstack`. Let's make branches grow, or join them when cells of
//  two branches get connected, and deploy a script with a few hundred cells
//  in a test.
const MAX_BRANCHES: usize = 16;
const MAX_BRANCH_SIZE: usize = 16;

/// An object-oriented representation of binary data
/// in hexadecimal format, which can be put into cells of the graph.
///
/// You can create it from Rust primitives:
///
/// ```
/// use sodg::Hex;
/// let d = Hex::from(65534);
/// assert_eq!("00-00-FF-FE", d.print());
/// ```
///
/// Then, you can turn it back to Rust primitives:
///
/// ```
/// use sodg::Hex;
/// let d = Hex::from(65534_i64);
/// assert_eq!(65534, d.to_i64().unwrap());
/// ```
#[derive(Serialize, Deserialize, Clone)]
pub enum Hex {
    Vector(Vec<u8>),
    Bytes([u8; HEX_SIZE], usize),
}

/// A label on an edge.
// @todo #313:60min `Label::Str` can't keep more than eight characters,
//  while attributes of EO objects may be longer, like `as-number`
//  (nine characters). Such a line of `phino sodg` output
//  fails in `Script::deploy_to()`. Let's make labels longer without
//  losing the `Copy` trait and test it with a long attribute.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Serialize, Deserialize)]
pub enum Label {
    Greek(char),
    Alpha(usize),
    Str([char; 8]),
}

/// What a cell of the graph stands for.
///
/// A cell that was never made by [`Sodg::formation`], [`Sodg::dispatch`],
/// or [`Sodg::application`] is [`Kind::Void`].
#[derive(PartialEq, Eq, Clone, Copy, Debug, Serialize, Deserialize)]
pub enum Kind {
    /// Nothing is known about the cell.
    Void,
    /// A formation, like `⟦ x ↦ ..., y ↦ ... ⟧`.
    Formation,
    /// A dispatch of the attribute, like `base.attr`; the base
    /// is the kid of the cell at the edge `π`.
    Dispatch(Label),
    /// An application with the attribute, like `proto( attr ↦ arg )`;
    /// the proto is the kid of the cell at the edge `π`, while the
    /// argument is the kid at the edge `attr`.
    Application(Label),
}

/// A wrapper of a plain text with graph-modifying instructions,
/// as printed by `phino sodg`.
///
/// For example, you can pass the following instructions to it:
///
/// ```text
/// F c0 foo
/// F c1 x
/// F c2
/// Δ c2 2A-
/// P c1 x c2
/// λ c1 L_foo
/// P c0 foo c1
/// ```
///
/// Each line is a command: a letter and its arguments, separated
/// by spaces. The names of cells, like `c0` above, are replaced by
/// autogenerated numbers during the deployment of this script to
/// a [`Sodg`].
pub struct Script {
    /// The text of it.
    txt: String,
    /// The names of cells dynamically discovered.
    vars: HashMap<String, usize>,
}

/// A struct that represents a Surging Object Di-Graph (SODG).
///
/// You make cells in it, attach them one to another with edges,
/// put data into some of them, and read data back, for example:
///
/// ```
/// use sodg::{Label, Sodg};
/// let mut sodg: Sodg<16> = Sodg::empty(256);
/// sodg.formation(0, &[Label::Alpha(0)]);
/// sodg.formation(1, &[Label::Alpha(1)]);
/// sodg.put(0, Label::Alpha(0), 1);
/// sodg.formation(2, &[]);
/// sodg.put(1, Label::Alpha(1), 2);
/// assert_eq!(1, sodg.kids(0).count());
/// assert_eq!(1, sodg.kids(1).count());
/// ```
///
/// This package is used in [reo](https://github.com/objectionary/reo)
/// project, as a memory model for objects and dependencies between them.
#[derive(Serialize, Deserialize)]
pub struct Sodg<const N: usize> {
    stores: emap::Map<usize>,
    branches: emap::Map<microstack::Stack<usize, MAX_BRANCH_SIZE>>,
    cells: emap::Map<Cell<N>>,
    /// This is the next ID of a cell to be returned by the [`Sodg::next_id`]
    /// function.
    #[serde(skip_serializing, skip_deserializing)]
    next_c: usize,
}

#[derive(PartialEq, Serialize, Deserialize, Clone)]
enum Persistence {
    Empty,
    Stored,
    Taken,
}

const BRANCH_NONE: usize = 0;
const BRANCH_STATIC: usize = 1;

#[derive(Serialize, Deserialize, Clone)]
struct Cell<const N: usize> {
    branch: usize,
    kind: Kind,
    attrs: Vec<Label>,
    data: Hex,
    persistence: Persistence,
    lambda: Option<String>,
    edges: micromap::Map<Label, usize, N>,
}

#[cfg(test)]
#[ctor::ctor]
fn init() {
    use log::LevelFilter;
    use simple_logger::SimpleLogger;

    SimpleLogger::new()
        .without_timestamps()
        .with_level(LevelFilter::Trace)
        .init()
        .unwrap();
}
