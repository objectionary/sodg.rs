// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

//! Interning of edge labels into compact numeric identifiers.

use rustc_hash::FxHashMap;

use crate::Label;

/// Identifier of an interned [`Label`].
pub type LabelId = u32;

/// Assigns a stable [`LabelId`] to every distinct [`Label`].
///
/// A [`Label`] is a wide value, because its `Str` variant carries eight
/// `char`s. Every edge of a vertex keeps one, and every lookup compares them
/// one by one. An identifier is four bytes, so a map keyed by identifiers
/// packs more edges into a cache line and compares them in a single
/// instruction.
///
/// Identifiers are handed out in the order of interning, starting from one,
/// which leaves zero free to denote the absence of a label.
///
/// ```
/// use sodg::{Label, LabelInterner};
/// let mut interner = LabelInterner::default();
/// let id = interner.intern(Label::Alpha(7));
/// assert_eq!(id, interner.intern(Label::Alpha(7)));
/// assert_eq!(Some(Label::Alpha(7)), interner.resolve(id));
/// ```
#[derive(Debug, Default, Clone)]
pub struct LabelInterner {
    ids: FxHashMap<Label, LabelId>,
    labels: Vec<Label>,
}

impl LabelInterner {
    /// Return the identifier of the label, assigning a new one if the label
    /// is seen for the first time.
    ///
    /// # Panics
    ///
    /// Panics if more than [`u32::MAX`] distinct labels are interned.
    pub fn intern(&mut self, label: Label) -> LabelId {
        if let Some(id) = self.ids.get(&label) {
            return *id;
        }
        let id = LabelId::try_from(self.labels.len() + 1).expect("Too many labels interned");
        self.ids.insert(label, id);
        self.labels.push(label);
        id
    }

    /// Return the identifier of an already interned label, or [`None`]
    /// if the label was never interned.
    #[must_use]
    pub fn get(&self, label: Label) -> Option<LabelId> {
        self.ids.get(&label).copied()
    }

    /// Return the label behind the identifier, or [`None`] if the identifier
    /// was never handed out by [`LabelInterner::intern`].
    #[must_use]
    pub fn resolve(&self, id: LabelId) -> Option<Label> {
        let index = usize::try_from(id).ok()?.checked_sub(1)?;
        self.labels.get(index).copied()
    }

    /// Return how many distinct labels are interned.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.labels.len()
    }

    /// Return `true` if nothing is interned yet.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.labels.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use super::*;

    #[test]
    fn assigns_the_same_id_to_equal_labels() {
        let mut interner = LabelInterner::default();
        assert_eq!(
            interner.intern(Label::Alpha(1)),
            interner.intern(Label::Alpha(1))
        );
    }

    #[test]
    fn assigns_different_ids_to_different_labels() {
        let mut interner = LabelInterner::default();
        assert_ne!(
            interner.intern(Label::Alpha(1)),
            interner.intern(Label::Alpha(2))
        );
    }

    #[test]
    fn tells_apart_labels_of_different_variants() {
        let mut interner = LabelInterner::default();
        assert_ne!(
            interner.intern(Label::Greek('α')),
            interner.intern(Label::from_str("α5").unwrap())
        );
    }

    #[test]
    fn never_assigns_zero() {
        let mut interner = LabelInterner::default();
        assert_ne!(0, interner.intern(Label::Greek('ρ')));
    }

    #[test]
    fn resolves_interned_label() {
        let mut interner = LabelInterner::default();
        let label = Label::from_str("foo").unwrap();
        let id = interner.intern(label);
        assert_eq!(Some(label), interner.resolve(id));
    }

    #[test]
    fn resolves_every_interned_label() {
        let mut interner = LabelInterner::default();
        let labels = [Label::Greek('φ'), Label::Alpha(0), Label::Alpha(9)];
        let ids: Vec<LabelId> = labels.iter().map(|l| interner.intern(*l)).collect();
        for (label, id) in labels.iter().zip(ids) {
            assert_eq!(Some(*label), interner.resolve(id));
        }
    }

    #[test]
    fn resolves_nothing_for_unknown_id() {
        let interner = LabelInterner::default();
        assert_eq!(None, interner.resolve(42));
    }

    #[test]
    fn resolves_nothing_for_zero() {
        let mut interner = LabelInterner::default();
        interner.intern(Label::Alpha(1));
        assert_eq!(None, interner.resolve(0));
    }

    #[test]
    fn finds_interned_label() {
        let mut interner = LabelInterner::default();
        let id = interner.intern(Label::Alpha(3));
        assert_eq!(Some(id), interner.get(Label::Alpha(3)));
    }

    #[test]
    fn finds_nothing_for_absent_label() {
        let interner = LabelInterner::default();
        assert_eq!(None, interner.get(Label::Alpha(3)));
    }

    #[test]
    fn counts_interned_labels() {
        let mut interner = LabelInterner::default();
        assert!(interner.is_empty());
        interner.intern(Label::Alpha(1));
        interner.intern(Label::Alpha(1));
        interner.intern(Label::Alpha(2));
        assert_eq!(2, interner.len());
    }

    #[test]
    fn keeps_ids_stable_while_growing() {
        let mut interner = LabelInterner::default();
        let first = interner.intern(Label::Alpha(1));
        for i in 2..100 {
            interner.intern(Label::Alpha(i));
        }
        assert_eq!(first, interner.intern(Label::Alpha(1)));
    }
}
