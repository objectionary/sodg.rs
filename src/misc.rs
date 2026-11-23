// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use crate::Sodg;

impl<const N: usize> Sodg<N> {
    /// Get total number of cells in the graph.
    #[must_use]
    pub fn len(&self) -> usize {
        self.keys().len()
    }

    /// Is it empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get keys of all cells alive?
    #[must_use]
    pub fn keys(&self) -> Vec<usize> {
        self.cells
            .iter()
            .filter(|(_, cell)| cell.made)
            .map(|(v, _)| v)
            .collect::<Vec<usize>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_cells() {
        let g: Sodg<16> = Sodg::empty(256);
        assert_eq!(0, g.len());
    }
}
