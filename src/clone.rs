// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use crate::Sodg;

impl<const N: usize> Clone for Sodg<N> {
    /// Make a clone of the graph.
    fn clone(&self) -> Self {
        Self {
            cells: self.cells.clone(),
            branches: self.branches.clone(),
            stores: self.stores.clone(),
            next_c: self.next_c,
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
        g.formation(1, &[]);
        g.formation(42, &[]);
        g.put(1, Label::Alpha(0), 42);
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
}
