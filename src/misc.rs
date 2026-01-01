// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use crate::Sodg;

impl<const N: usize> Sodg<N> {
    /// Get total number of vertices in the graph.
    #[must_use]
    pub fn len(&self) -> usize {
        self.keys().len()
    }

    /// Is it empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get keys of all vertices alive?
    #[must_use]
    pub fn keys(&self) -> Vec<usize> {
        self.vertices
            .iter()
            .filter(|(_, vtx)| vtx.branch != 0)
            .map(|(v, _)| v)
            .collect::<Vec<usize>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_vertices() {
        let g: Sodg<16> = Sodg::empty(256);
        assert_eq!(0, g.len());
    }
}
