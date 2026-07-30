// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

//! Interning of edge labels into compact numeric identifiers.

use std::collections::HashMap;

use crate::Label;

/// Identifier of an interned [`Label`].
pub type LabelId = u32;

/// Assigns a stable [`LabelId`] to every distinct [`Label`].
///
/// Labels are compared by their textual representation, so two labels that
/// print the same share one identifier. Identifiers start at one, which lets
/// zero denote the absence of a label.
///
/// # Examples
///
/// ```
/// use sodg::{Label, LabelInterner};
/// let mut interner = LabelInterner::default();
/// let id = interner.intern(&Label::Alpha(7));
/// assert_eq!(id, interner.intern(&Label::Alpha(7)));
/// assert_eq!(Some("α7"), interner.resolve(id));
/// ```
#[derive(Debug, Default, Clone)]
pub struct LabelInterner {
    ids: HashMap<String, LabelId>,
    texts: Vec<String>,
}

impl LabelInterner {
    /// Return the identifier of the label, assigning a new one if needed.
    ///
    /// # Panics
    ///
    /// Panics if more than [`u32::MAX`] distinct labels were interned.
    pub fn intern(&mut self, label: &Label) -> LabelId {
        let text = label.to_string();
        if let Some(id) = self.ids.get(&text) {
            return *id;
        }
        let id = LabelId::try_from(self.texts.len() + 1).expect("too many labels interned");
        self.ids.insert(text.clone(), id);
        self.texts.push(text);
        id
    }

    /// Return the identifier of an already interned label.
    #[must_use]
    pub fn get(&self, label: &Label) -> Option<LabelId> {
        self.ids.get(&label.to_string()).copied()
    }

    /// Return the text of the label behind the identifier.
    #[must_use]
    pub fn resolve(&self, id: LabelId) -> Option<&str> {
        let index = usize::try_from(id).ok()?.checked_sub(1)?;
        self.texts.get(index).map(String::as_str)
    }

    /// Return how many distinct labels are interned.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.texts.len()
    }

    /// Return `true` if nothing is interned yet.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.texts.is_empty()
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
            interner.intern(&Label::Alpha(1)),
            interner.intern(&Label::Alpha(1))
        );
    }

    #[test]
    fn assigns_different_ids_to_different_labels() {
        let mut interner = LabelInterner::default();
        assert_ne!(
            interner.intern(&Label::Alpha(1)),
            interner.intern(&Label::Alpha(2))
        );
    }

    #[test]
    fn never_assigns_zero() {
        let mut interner = LabelInterner::default();
        assert_ne!(0, interner.intern(&Label::Greek('ρ')));
    }

    #[test]
    fn resolves_interned_label() {
        let mut interner = LabelInterner::default();
        let id = interner.intern(&Label::from_str("foo").unwrap());
        assert_eq!(Some("foo"), interner.resolve(id));
    }

    #[test]
    fn resolves_nothing_for_unknown_id() {
        let interner = LabelInterner::default();
        assert_eq!(None, interner.resolve(42));
    }

    #[test]
    fn finds_interned_label() {
        let mut interner = LabelInterner::default();
        let id = interner.intern(&Label::Alpha(3));
        assert_eq!(Some(id), interner.get(&Label::Alpha(3)));
    }

    #[test]
    fn finds_nothing_for_absent_label() {
        let interner = LabelInterner::default();
        assert_eq!(None, interner.get(&Label::Alpha(3)));
    }

    #[test]
    fn counts_interned_labels() {
        let mut interner = LabelInterner::default();
        assert!(interner.is_empty());
        interner.intern(&Label::Alpha(1));
        interner.intern(&Label::Alpha(1));
        interner.intern(&Label::Alpha(2));
        assert_eq!(2, interner.len());
    }
}
