// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use crate::{BRANCH_NONE, Sodg};

impl<const N: usize> Sodg<N> {
    /// Get next unique ID of a vertex.
    ///
    /// This ID will never be returned by [`Sodg::next_id`] again. Also, this ID will not
    /// be equal to any of the existing IDs of vertices.
    ///
    /// # Panics
    ///
    /// May panic if not enough IDs are available.
    #[inline]
    pub fn next_id(&mut self) -> usize {
        let capacity = self.vertex_capacity;
        let mut id = self.next_v;
        while id < capacity {
            let available =
                self.vertices.get(id).is_none_or(|vertex| vertex.branch == BRANCH_NONE);
            if available {
                break;
            }
            id += 1;
        }
        assert!(id < capacity, "Not enough vertex identifiers available");
        if id + 1 > self.next_v {
            self.next_v = id + 1;
        }
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_next_id() {
        let mut g: Sodg<16> = Sodg::empty(256);
        assert_eq!(0, g.next_id());
        assert_eq!(1, g.next_id());
        assert_eq!(2, g.next_id());
    }

    #[test]
    fn calculates_next_id() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(42);
        assert_eq!(1, g.next_id());
        assert_eq!(2, g.next_id());
    }

    #[test]
    fn next_id_after_inject() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        assert_eq!(0, g.next_id());
        assert_eq!(2, g.next_id());
    }

    #[test]
    fn next_id_after_sequence() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        assert_eq!(2, g.next_id());
        assert_eq!(3, g.next_id());
    }

    #[test]
    fn next_id_after_zero() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        assert_eq!(1, g.next_id());
        assert_eq!(2, g.next_id());
    }
}
