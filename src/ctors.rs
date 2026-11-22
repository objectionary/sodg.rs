// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use emap::Map;

use crate::{Cell, Hex, Kind, MAX_BRANCHES, Persistence, Sodg};

impl<const N: usize> Sodg<N> {
    /// Make an empty [`Sodg`], with no cells and no edges.
    ///
    /// # Panics
    ///
    /// May panic if cells provided to alerts are absent (should never happen, though).
    #[must_use]
    pub fn empty(cap: usize) -> Self {
        let mut g = Self {
            cells: Map::with_capacity_some(
                cap,
                Cell {
                    branch: 0,
                    kind: Kind::Void,
                    attrs: Vec::new(),
                    data: Hex::empty(),
                    persistence: Persistence::Empty,
                    lambda: None,
                    edges: micromap::Map::new(),
                },
            ),
            stores: Map::with_capacity_some(MAX_BRANCHES, 0),
            branches: Map::with_capacity_some(MAX_BRANCHES, microstack::Stack::new()),
            next_c: 0,
        };
        g.branches.insert(0, microstack::Stack::from_vec(vec![0]));
        g.branches.insert(1, microstack::Stack::from_vec(vec![0]));
        g
    }
}

#[test]
fn makes_an_empty_sodg() {
    let mut g: Sodg<16> = Sodg::empty(256);
    g.formation(0, &[]);
    assert_eq!(1, g.len());
}
