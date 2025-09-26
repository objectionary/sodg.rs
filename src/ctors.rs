// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use emap::Map;

use crate::{
    BranchMembers, EdgeIndex, Hex, LabelInterner, MAX_BRANCHES, Persistence, Sodg, Vertex,
};

impl<const N: usize> Sodg<N> {
    /// Make an empty [`Sodg`], with no vertices and no edges.
    ///
    /// # Panics
    ///
    /// May panic if vertices provided to alerts are absent (should never happen, though).
    #[must_use]
    pub fn empty(cap: usize) -> Self {
        let mut g = Self {
            vertices: Map::with_capacity_some(
                cap,
                Vertex {
                    branch: 0,
                    data: Hex::empty(),
                    persistence: Persistence::Empty,
                    edges: Vec::new(),
                    index: EdgeIndex::new(),
                },
            ),
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
