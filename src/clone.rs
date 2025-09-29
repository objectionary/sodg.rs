// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use crate::Sodg;

impl<const N: usize> Clone for Sodg<N> {
    /// Make a clone of the graph.
    fn clone(&self) -> Self {
        Self {
            vertex_capacity: self.vertex_capacity,
            vertices: self.vertices.clone(),
            branches: self.branches.clone(),
            stores: self.stores.clone(),
            labels: self.labels.clone(),
            next_v: self.next_v,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Label;

    #[test]
    fn makes_a_clone() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(42);
        g.bind(1, 42, Label::Alpha(0)).unwrap();
        let c = g.clone();
        assert_eq!(2, c.len());
    }

    #[test]
    #[allow(clippy::redundant_clone)]
    fn makes_an_empty_clone() {
        let g: Sodg<16> = Sodg::empty(256);
        let c = g.clone();
        assert_eq!(0, c.len());
    }

    #[test]
    fn cloned_graph_allows_new_vertices() {
        let g: Sodg<16> = Sodg::empty(256);
        let mut clone = g.clone();
        assert!(clone.vertices.get(7).is_none());
        clone.add(7);
        assert!(clone.vertices.get(7).is_some());
    }
}
