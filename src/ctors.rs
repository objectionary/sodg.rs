// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use emap::Map;

use crate::{BranchMembers, LabelInterner, MAX_BRANCHES, Sodg};

impl<const N: usize> Sodg<N> {
    /// Make an empty [`Sodg`], with no vertices and no edges.
    ///
    /// # Panics
    ///
    /// May panic if vertices provided to alerts are absent (should never happen, though).
    #[must_use]
    pub fn empty(cap: usize) -> Self {
        let mut g = Self {
            vertex_capacity: cap,
            vertices: Map::with_capacity_none(cap),
            stores: Map::with_capacity_some(MAX_BRANCHES, 0),
            branches: Map::with_capacity_some(MAX_BRANCHES, BranchMembers::new()),
            labels: LabelInterner::default(),
            next_v: 0,
        };
        g.branches.insert(0, BranchMembers::from_vec(vec![0]));
        g.branches.insert(1, BranchMembers::from_vec(vec![0]));
        g
    }
}

#[test]
fn makes_an_empty_sodg() {
    let mut g: Sodg<16> = Sodg::empty(256);
    g.add(0);
    assert_eq!(1, g.len());
}
