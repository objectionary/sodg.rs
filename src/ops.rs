// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use anyhow::Context as _;
#[cfg(debug_assertions)]
use log::trace;

use crate::{BRANCH_NONE, BRANCH_STATIC, Persistence, Sodg};
use crate::{Hex, Kind, Label};

impl<const N: usize> Sodg<N> {
    /// Make the cell `c` a formation with the attributes `attrs`
    /// (the command `F c attr0 attr1 ...`).
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Kind, Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// let x = Label::from_str("x").unwrap();
    /// g.formation(1, &[x]);
    /// assert_eq!(Kind::Formation, g.kind(1));
    /// assert_eq!(&[x], g.attrs(1));
    /// ```
    ///
    /// If the cell `c` already exists, its kind and attributes
    /// are replaced, while its edges stay.
    ///
    /// # Panics
    ///
    /// If the cell `c` is out of the capacity of the graph.
    #[inline]
    pub fn formation(&mut self, c: usize, attrs: &[Label]) {
        self.make(c);
        let cell = self.cells.get_mut(c).unwrap();
        cell.kind = Kind::Formation;
        cell.attrs = attrs.to_vec();
        #[cfg(debug_assertions)]
        trace!("#formation: c{c} made with {} attribute(s)", attrs.len());
    }

    /// Make the cell `c` a dispatch of the attribute `attr` from the
    /// cell `base` (the command `D c base attr`).
    ///
    /// The cell gets the kind [`Kind::Dispatch`] with `attr` inside
    /// and the edge `π` to `base`. For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Kind, Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// let x = Label::from_str("x").unwrap();
    /// g.formation(1, &[x]);
    /// g.dispatch(4, 1, x);
    /// assert_eq!(Kind::Dispatch(x), g.kind(4));
    /// assert_eq!(1, g.kid(4, Label::Greek('π')).unwrap());
    /// ```
    ///
    /// # Panics
    ///
    /// If either cell is out of the capacity of the graph.
    #[inline]
    pub fn dispatch(&mut self, c: usize, base: usize, attr: Label) {
        self.make(c);
        let cell = self.cells.get_mut(c).unwrap();
        cell.kind = Kind::Dispatch(attr);
        cell.attrs.clear();
        self.link(c, base, Label::Greek('π'));
        #[cfg(debug_assertions)]
        trace!("#dispatch: c{c} made as c{base}.{attr}");
    }

    /// Make the cell `c` an application of the cell `proto` with
    /// the cell `arg` bound to the attribute `attr`
    /// (the command `A c proto attr arg`).
    ///
    /// The cell gets the kind [`Kind::Application`] with `attr` inside,
    /// the edge `π` to `proto`, and the edge `attr` to `arg`. For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Kind, Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// let z = Label::from_str("z").unwrap();
    /// g.formation(3, &[z]);
    /// g.formation(4, &[]);
    /// g.application(5, 3, z, 4);
    /// assert_eq!(Kind::Application(z), g.kind(5));
    /// assert_eq!(3, g.kid(5, Label::Greek('π')).unwrap());
    /// assert_eq!(4, g.kid(5, z).unwrap());
    /// ```
    ///
    /// # Panics
    ///
    /// If any cell is out of the capacity of the graph.
    #[inline]
    pub fn application(&mut self, c: usize, proto: usize, attr: Label, arg: usize) {
        self.make(c);
        let cell = self.cells.get_mut(c).unwrap();
        cell.kind = Kind::Application(attr);
        cell.attrs.clear();
        self.link(c, proto, Label::Greek('π'));
        self.link(c, arg, attr);
        #[cfg(debug_assertions)]
        trace!("#application: c{c} made as c{proto}({attr} ↦ c{arg})");
    }

    /// Put the cell `kid` to the attribute `attr` of the cell `c`
    /// (the command `P c attr kid`), making an edge from `c` to `kid`.
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// let x = Label::from_str("x").unwrap();
    /// g.formation(1, &[x]);
    /// g.formation(2, &[]);
    /// g.put(1, x, 2);
    /// assert_eq!(2, g.kid(1, x).unwrap());
    /// ```
    ///
    /// If the attribute already has a kid, it is replaced.
    ///
    /// # Panics
    ///
    /// If either cell is out of the capacity of the graph.
    #[inline]
    pub fn put(&mut self, c: usize, attr: Label, kid: usize) {
        self.link(c, kid, attr);
    }

    /// Set the Δ-asset of the cell `c` (the command `Δ c data`).
    ///
    /// For example:
    ///
    /// ```
    /// use sodg::{Hex, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.formation(2, &[]);
    /// g.delta(2, &Hex::from(42_i64));
    /// assert_eq!(42, g.data(2).unwrap().to_i64().unwrap());
    /// ```
    ///
    /// # Panics
    ///
    /// If the cell `c` is out of the capacity of the graph.
    #[inline]
    pub fn delta(&mut self, c: usize, d: &Hex) {
        let cell = self.cells.get_mut(c).unwrap();
        if cell.persistence != Persistence::Stored {
            *self.stores.get_mut(cell.branch).unwrap() += 1;
        }
        cell.persistence = Persistence::Stored;
        cell.data = d.clone();
        #[cfg(debug_assertions)]
        trace!("#delta: data of c{c} set to {d}");
    }

    /// Set the λ-asset of the cell `c` (the command `λ c name`).
    ///
    /// For example:
    ///
    /// ```
    /// use sodg::Sodg;
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.formation(1, &[]);
    /// g.lambda(1, "L_foo");
    /// assert_eq!(Some("L_foo"), g.atom(1));
    /// ```
    ///
    /// # Panics
    ///
    /// If the cell `c` is out of the capacity of the graph.
    #[inline]
    pub fn lambda(&mut self, c: usize, name: &str) {
        self.cells.get_mut(c).unwrap().lambda = Some(name.to_string());
        #[cfg(debug_assertions)]
        trace!("#lambda: λ-asset of c{c} set to {name}");
    }

    /// Get the kind of the cell `c`.
    ///
    /// # Panics
    ///
    /// If the cell `c` is out of the capacity of the graph.
    #[must_use]
    #[inline]
    pub fn kind(&self, c: usize) -> Kind {
        self.cells.get(c).unwrap().kind
    }

    /// Get the attributes of the formation in the cell `c`, in the order
    /// they were given to [`Sodg::formation`], including those without kids.
    ///
    /// # Panics
    ///
    /// If the cell `c` is out of the capacity of the graph.
    #[must_use]
    #[inline]
    pub fn attrs(&self, c: usize) -> &[Label] {
        &self.cells.get(c).unwrap().attrs
    }

    /// Get the name of the λ-asset of the cell `c`, if it was set
    /// by [`Sodg::lambda`].
    ///
    /// # Panics
    ///
    /// If the cell `c` is out of the capacity of the graph.
    #[must_use]
    #[inline]
    pub fn atom(&self, c: usize) -> Option<&str> {
        self.cells.get(c).unwrap().lambda.as_deref()
    }

    /// Make the cell `c` alive, if it is not alive yet.
    pub(crate) fn make(&mut self, c: usize) {
        let cell = self.cells.get_mut(c).unwrap();
        if cell.branch == BRANCH_NONE {
            cell.branch = BRANCH_STATIC;
        }
    }

    /// Make an edge from the cell `c1` to the cell `c2` and put
    /// the label `a` on it, replacing the edge with the same label, if any.
    pub(crate) fn link(&mut self, c1: usize, c2: usize, a: Label) {
        let mut ours = self.cells.get(c1).unwrap().branch;
        let theirs = self.cells.get(c2).unwrap().branch;
        self.cells.get_mut(c1).unwrap().edges.insert(a, c2);
        if ours == BRANCH_STATIC {
            if theirs == BRANCH_STATIC {
                for b in self.branches.iter_mut() {
                    if b.1.is_empty() {
                        b.1.push(c1);
                        ours = b.0;
                        break;
                    }
                }
                self.relocate(c1, ours, false);
                self.relocate(c2, ours, true);
            } else {
                self.relocate(c1, theirs, true);
            }
        } else if self.cells.get(c2).unwrap().branch == BRANCH_STATIC {
            self.relocate(c2, ours, true);
        }
        #[cfg(debug_assertions)]
        trace!(
            "#link: edge added c{}(b={}).{} → c{}(b={})",
            c1,
            self.cells.get(c1).unwrap().branch,
            a,
            c2,
            self.cells.get(c2).unwrap().branch,
        );
    }

    /// Move the cell `c` from the static branch into the branch `b`,
    /// carrying its stored data along, so that the branch knows
    /// how many cells with data it has.
    fn relocate(&mut self, c: usize, b: usize, push: bool) {
        let cell = self.cells.get_mut(c).unwrap();
        let before = cell.branch;
        cell.branch = b;
        if cell.persistence == Persistence::Stored {
            *self.stores.get_mut(before).unwrap() -= 1;
            *self.stores.get_mut(b).unwrap() += 1;
        }
        if push {
            self.branches.get_mut(b).unwrap().push(c);
        }
    }

    /// Read cell data, and then submit the cell to garbage collection.
    ///
    /// For example:
    ///
    /// ```
    /// use sodg::Hex;
    /// use sodg::Sodg;
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.formation(42, &[]);
    /// let data = Hex::from_str_bytes("hello, world!");
    /// g.delta(42, &data);
    /// assert_eq!(data, g.data(42).unwrap());
    /// ```
    ///
    /// If there is no data, `None` will be returned, for example:
    ///
    /// ```
    /// use sodg::Sodg;
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.formation(42, &[]);
    /// assert!(g.data(42).is_none());
    /// ```
    ///
    /// # Panics
    ///
    /// If the cell `c` is absent, it will panic.
    #[inline]
    pub fn data(&mut self, c: usize) -> Option<Hex> {
        let cell = self.cells.get_mut(c).unwrap();
        match cell.persistence {
            Persistence::Stored => {
                let d = cell.data.clone();
                cell.persistence = Persistence::Taken;
                let branch = cell.branch;
                let s = self.stores.get_mut(branch).unwrap();
                *s -= 1;
                if *s == 0 {
                    let members = self.branches.get_mut(branch).unwrap();
                    for m in members.into_iter() {
                        self.cells.get_mut(m).unwrap().branch = BRANCH_NONE;
                    }
                    #[cfg(debug_assertions)]
                    trace!(
                        "#data: branch no.{} destroyed {} cells as garbage: {}",
                        branch,
                        members.len(),
                        members
                            .into_iter()
                            .map(|m| format!("c{m}"))
                            .collect::<Vec<String>>()
                            .join(", ")
                    );
                    members.clear();
                }
                #[cfg(debug_assertions)]
                trace!("#data: data of c{c} retrieved");
                Some(d)
            }
            Persistence::Taken => {
                #[cfg(debug_assertions)]
                trace!("#data: data of c{c} retrieved again");
                Some(cell.data.clone())
            }
            Persistence::Empty => None,
        }
    }

    /// Find all kids of a cell.
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.formation(0, &[]);
    /// g.formation(42, &[]);
    /// g.put(0, Label::from_str("k").unwrap(), 42);
    /// let (a, to) = g.kids(0).next().unwrap().clone();
    /// assert_eq!("k", a.to_string());
    /// assert_eq!(42, *to);
    /// ```
    ///
    /// Just in case, if you need to put all names into a single line:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use itertools::Itertools;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.formation(0, &[]);
    /// g.formation(42, &[]);
    /// g.put(0, Label::from_str("a").unwrap(), 42);
    /// g.put(0, Label::from_str("b").unwrap(), 42);
    /// g.put(0, Label::from_str("c").unwrap(), 42);
    /// let mut names = g.kids(0).into_iter().map(|(a, _)| a.to_string()).collect::<Vec<String>>();
    /// names.sort();
    /// assert_eq!("a,b,c", names.join(","));
    /// ```
    ///
    /// # Panics
    ///
    /// If the cell `c` is absent, `Err` will be returned.
    #[inline]
    pub fn kids(&self, c: usize) -> impl Iterator<Item = (&Label, &usize)> + '_ {
        self.cells
            .get(c)
            .with_context(|| format!("Can't find c{c} in kids()"))
            .unwrap()
            .edges
            .iter()
    }

    /// Find a kid of a cell, by its edge name, and return the ID of the cell found.
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.formation(0, &[]);
    /// g.formation(42, &[]);
    /// let k = Label::from_str("k").unwrap();
    /// g.put(0, k, 42);
    /// assert_eq!(42, g.kid(0, k).unwrap());
    /// ```
    ///
    /// # Panics
    ///
    /// If the cell `c` is absent, it will panic.
    #[must_use]
    #[inline]
    pub fn kid(&self, c: usize, a: Label) -> Option<usize> {
        for e in &self.cells.get(c).unwrap().edges {
            if *e.0 == a {
                return Some(*e.1);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use super::*;

    fn label(s: &str) -> Label {
        Label::from_str(s).unwrap()
    }

    #[test]
    fn makes_simple_formation() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[Label::Alpha(0)]);
        g.formation(2, &[]);
        g.put(1, Label::Alpha(0), 2);
        assert_eq!(2, g.len());
        assert_eq!(Kind::Formation, g.kind(1));
    }

    #[test]
    fn keeps_void_attributes_of_formation() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(7, &[label("z"), label("t")]);
        assert_eq!(&[label("z"), label("t")], g.attrs(7));
        assert_eq!(0, g.kids(7).count());
    }

    #[test]
    fn sets_branch_correctly() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.put(1, Label::Alpha(0), 2);
        assert_eq!(1, g.branches.get(1).unwrap().len());
        assert_eq!(2, g.branches.get(2).unwrap().len());
        g.delta(2, &Hex::from(42));
        assert_eq!(&1, g.stores.get(2).unwrap());
        g.formation(3, &[]);
        g.put(1, Label::Alpha(1), 3);
        assert_eq!(3, g.branches.get(2).unwrap().len());
        g.formation(4, &[]);
        g.formation(5, &[]);
        g.put(4, Label::Alpha(0), 5);
        assert_eq!(2, g.branches.get(3).unwrap().len());
        g.data(2);
        assert_eq!(0, g.branches.get(2).unwrap().len());
    }

    #[test]
    fn carries_data_into_dynamic_branch() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[label("x")]);
        g.formation(2, &[]);
        g.delta(2, &Hex::from(42_i64));
        g.put(1, label("x"), 2);
        let branch = g.cells.get(2).unwrap().branch;
        assert_eq!(&1, g.stores.get(branch).unwrap());
        assert_eq!(&0, g.stores.get(BRANCH_STATIC).unwrap());
        assert_eq!(42, g.data(2).unwrap().to_i64().unwrap());
    }

    #[test]
    fn makes_dispatch() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[label("x")]);
        g.dispatch(4, 1, label("x"));
        assert_eq!(Kind::Dispatch(label("x")), g.kind(4));
        assert_eq!(1, g.kid(4, Label::Greek('π')).unwrap());
        assert_eq!(1, g.kids(4).count());
    }

    #[test]
    fn makes_application() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(3, &[label("z")]);
        g.formation(4, &[]);
        g.application(5, 3, label("z"), 4);
        assert_eq!(Kind::Application(label("z")), g.kind(5));
        assert_eq!(3, g.kid(5, Label::Greek('π')).unwrap());
        assert_eq!(4, g.kid(5, label("z")).unwrap());
    }

    #[test]
    fn sets_lambda() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        assert!(g.atom(1).is_none());
        g.lambda(1, "Lorg_eolang_number_plus");
        assert_eq!(Some("Lorg_eolang_number_plus"), g.atom(1));
    }

    #[test]
    fn knows_void_kind() {
        let g: Sodg<16> = Sodg::empty(256);
        assert_eq!(Kind::Void, g.kind(3));
    }

    #[test]
    fn fetches_kid() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        let k = label("hello");
        g.put(1, k, 2);
        assert_eq!(2, g.kid(1, k).unwrap());
    }

    #[test]
    fn puts_two_names() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        let first = label("first");
        g.put(1, first, 2);
        let second = label("second");
        g.put(1, second, 2);
        assert_eq!(2, g.kid(1, first).unwrap());
        assert_eq!(2, g.kid(1, second).unwrap());
    }

    #[test]
    fn overwrites_edge() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.put(1, label("foo"), 2);
        g.formation(3, &[]);
        g.put(1, label("foo"), 3);
        assert_eq!(3, g.kid(1, label("foo")).unwrap());
    }

    #[test]
    fn moves_static_cells_into_dynamic_branch() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.put(1, Label::Alpha(0), 2);
        let branch = g.cells.get(1).unwrap().branch;
        assert_ne!(BRANCH_STATIC, branch);
        assert_eq!(branch, g.cells.get(2).unwrap().branch);
        let members: Vec<usize> = g.branches.get(branch).unwrap().iter().copied().collect();
        assert!(members.contains(&1));
        assert!(members.contains(&2));
    }

    #[test]
    fn joins_static_cell_to_existing_branch() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.put(1, Label::Alpha(0), 2);
        let dynamic_branch = g.cells.get(1).unwrap().branch;
        g.formation(3, &[]);
        assert_eq!(BRANCH_STATIC, g.cells.get(3).unwrap().branch);
        g.put(3, Label::Alpha(1), 1);
        assert_eq!(dynamic_branch, g.cells.get(3).unwrap().branch);
        let members: Vec<usize> = g
            .branches
            .get(dynamic_branch)
            .unwrap()
            .iter()
            .copied()
            .collect();
        assert_eq!(3, members.len());
        assert!(members.contains(&1));
        assert!(members.contains(&2));
        assert!(members.contains(&3));
    }

    #[test]
    fn promotes_target_from_static_branch() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.put(1, Label::Alpha(0), 2);
        let dynamic_branch = g.cells.get(1).unwrap().branch;
        g.formation(3, &[]);
        assert_eq!(BRANCH_STATIC, g.cells.get(3).unwrap().branch);
        g.put(1, Label::Alpha(1), 3);
        assert_eq!(dynamic_branch, g.cells.get(3).unwrap().branch);
        let members: Vec<usize> = g
            .branches
            .get(dynamic_branch)
            .unwrap()
            .iter()
            .copied()
            .collect();
        assert!(members.contains(&1));
        assert!(members.contains(&2));
        assert!(members.contains(&3));
    }

    #[test]
    fn puts_to_root() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, label("x"), 1);
        assert!(g.kid(0, label("ρ")).is_none());
        assert!(g.kid(0, label("σ")).is_none());
    }

    #[test]
    fn sets_simple_data() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let data = Hex::from_str_bytes("hello");
        g.formation(0, &[]);
        g.delta(0, &data);
        assert_eq!(data, g.data(0).unwrap());
    }

    #[test]
    fn collects_garbage() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.put(1, Label::Alpha(0), 2);
        g.delta(2, &Hex::from_str_bytes("hello"));
        g.formation(3, &[]);
        g.put(1, Label::Alpha(0), 3);
        assert_eq!(3, g.len());
        assert_eq!(3, g.branches.get(2).unwrap().len());
        g.data(2);
        assert_eq!(0, g.len());
    }

    #[test]
    fn finds_all_kids() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, label("one"), 1);
        g.put(0, label("two"), 1);
        assert_eq!(2, g.kids(0).count());
        let mut names = vec![];
        for (a, to) in g.kids(0) {
            names.push(format!("{a}/{to}"));
        }
        names.sort();
        assert_eq!("one/1,two/1", names.join(","));
    }

    #[test]
    fn builds_list_of_kids() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, label("one"), 1);
        g.put(0, label("two"), 1);
        g.put(0, label("three"), 1);
        let mut names: Vec<String> = g.kids(0).map(|(a, _)| format!("{a}")).collect();
        names.sort();
        assert_eq!("one,three,two", names.join(","));
    }

    #[test]
    fn gets_data_from_empty_cell() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        assert!(g.data(0).is_none());
    }

    #[test]
    fn gets_absent_kid() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        assert!(g.kid(0, label("hello")).is_none());
    }

    #[test]
    fn gets_kid_from_absent_cell() {
        let g: Sodg<16> = Sodg::empty(256);
        assert!(g.kid(0, label("hello")).is_none());
    }

    #[test]
    fn makes_formation_twice() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(0, &[label("x")]);
        assert_eq!(1, g.len());
        assert_eq!(&[label("x")], g.attrs(0));
    }
}
