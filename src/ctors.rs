// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use emap::Map;

use crate::{Cell, Kind, Sodg};

impl<const N: usize> Sodg<N> {
    /// Make an empty [`Sodg`], with no cells and no edges.
    ///
    /// # Panics
    ///
    /// May panic if cells provided to alerts are absent (should never happen, though).
    #[must_use]
    pub fn empty(cap: usize) -> Self {
        Self {
            cells: Map::with_capacity_some(
                cap,
                Cell {
                    made: false,
                    kind: Kind::Void,
                    attrs: Vec::new(),
                    data: None,
                    lambda: None,
                    edges: micromap::Map::new(),
                },
            ),
            next_c: 0,
        }
    }
}

#[test]
fn makes_an_empty_sodg() {
    let mut g: Sodg<16> = Sodg::empty(256);
    g.formation(0, &[]);
    assert_eq!(1, g.len());
}
