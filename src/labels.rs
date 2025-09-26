// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

//! Label interning utilities.
//!
//! The historic [`Label`] enum models structured edge labels, while the
//! related issue expects labels to behave like `&str`. Instead of replacing the
//! enum with a string-based representation, we canonicalize every [`Label`]
//! into its string form at the interning boundary. This keeps the enum-based
//! API intact while ensuring that external integrations relying on `&str`
//! semantics continue to operate on stable UTF-8 text identifiers.

use std::collections::HashMap;
use std::fmt::{Display, Formatter, Result as FmtResult};

use serde::{Deserialize, Serialize};

use crate::Label;

/// Identifier of an interned label.
pub type LabelId = u32;

/// Errors that may occur while working with a [`LabelInterner`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LabelInternerError {
    /// The number of unique labels exceeded the representable [`LabelId`] range.
    CapacityExceeded,
}

impl Display for LabelInternerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::CapacityExceeded => f.write_str("label pool exhausted"),
        }
    }
}

impl std::error::Error for LabelInternerError {}

/// Maintains a bijection between labels and compact identifiers.
///
/// The interner stores labels by their canonical UTF-8 representation while
/// preserving stable numeric identifiers. `0` is reserved to denote a missing
/// label.
///
/// # Invariants
///
/// * Every identifier returned by [`get_or_intern`](Self::get_or_intern) maps to
///   exactly one canonical UTF-8 label.
/// * Identifier `0` is never allocated and signals "no label" in serialized
///   structures.
/// * Re-interning an existing label always yields the same identifier.
///
/// # Examples
///
/// ```
/// use std::str::FromStr as _;
/// use sodg::{Label, LabelInterner};
///
/// let mut interner = LabelInterner::default();
/// let alpha = Label::Alpha(7);
/// let hello = Label::from_str("hello").unwrap();
/// let alpha_id = interner.get_or_intern(&alpha).unwrap();
/// let hello_id = interner.get_or_intern(&hello).unwrap();
/// assert_eq!(Some(alpha_id), interner.get(&alpha));
/// assert_eq!(Some("hello"), interner.resolve(hello_id));
/// ```
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct LabelInterner {
    forward: HashMap<String, LabelId>,
    reverse: HashMap<LabelId, String>,
    #[serde(default)]
    next: NextLabelId,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(transparent)]
struct NextLabelId(LabelId);

impl Default for NextLabelId {
    fn default() -> Self {
        Self(1)
    }
}

impl NextLabelId {
    const fn allocate(&mut self) -> Result<LabelId, LabelInternerError> {
        let current = self.0;
        if current == LabelId::MAX {
            return Err(LabelInternerError::CapacityExceeded);
        }
        self.0 = current + 1;
        Ok(current)
    }
}

impl LabelInterner {
    /// Ensure the provided [`Label`] has a stable identifier.
    ///
    /// # Errors
    ///
    /// Returns [`LabelInternerError::CapacityExceeded`] if there is no free
    /// identifier left.
    ///
    /// # Examples
    ///
    /// ```
    /// use sodg::{Label, LabelInterner};
    ///
    /// let mut interner = LabelInterner::default();
    /// let id = interner.get_or_intern(&Label::Alpha(0)).unwrap();
    /// assert_eq!(Some(id), interner.get(&Label::Alpha(0)));
    /// ```
    pub fn get_or_intern(&mut self, label: &Label) -> Result<LabelId, LabelInternerError> {
        let key = canonical_form(label);
        if let Some(id) = self.forward.get(&key) {
            return Ok(*id);
        }
        let id = self.next.allocate()?;
        self.forward.insert(key.clone(), id);
        self.reverse.insert(id, key);
        Ok(id)
    }

    /// Retrieve the identifier previously assigned to [`label`](Label).
    ///
    /// # Examples
    ///
    /// ```
    /// use sodg::{Label, LabelInterner};
    ///
    /// let mut interner = LabelInterner::default();
    /// interner.get_or_intern(&Label::Alpha(1)).unwrap();
    /// assert!(interner.get(&Label::Alpha(1)).is_some());
    /// assert!(interner.get(&Label::Alpha(99)).is_none());
    /// ```
    #[must_use]
    pub fn get(&self, label: &Label) -> Option<LabelId> {
        let key = canonical_form(label);
        self.forward.get(&key).copied()
    }

    /// Resolve an identifier into its canonical UTF-8 label.
    ///
    /// # Examples
    ///
    /// ```
    /// use sodg::{Label, LabelInterner};
    ///
    /// let mut interner = LabelInterner::default();
    /// let id = interner.get_or_intern(&Label::Alpha(2)).unwrap();
    /// assert_eq!(Some("α2"), interner.resolve(id));
    /// assert_eq!(None, interner.resolve(0));
    /// ```
    pub fn resolve(&self, id: LabelId) -> Option<&str> {
        if id == 0 {
            return None;
        }
        self.reverse.get(&id).map(String::as_str)
    }
}

fn canonical_form(label: &Label) -> String {
    match label {
        Label::Greek(ch) => ch.to_string(),
        Label::Alpha(idx) => format!("α{idx}"),
        Label::Str(chars) => chars.iter().filter(|ch| **ch != ' ').collect(),
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use bincode::serde;

    use super::*;

    #[test]
    fn interns_labels_once() {
        let mut interner = LabelInterner::default();
        let label = Label::Alpha(0);
        let first = interner.get_or_intern(&label).unwrap();
        let second = interner.get_or_intern(&label).unwrap();
        assert_eq!(first, second);
    }

    #[test]
    fn get_returns_existing_identifier() {
        let mut interner = LabelInterner::default();
        let label = Label::Greek('λ');
        let id = interner.get_or_intern(&label).unwrap();
        assert_eq!(Some(id), interner.get(&label));
    }

    #[test]
    fn resolve_returns_none_for_missing() {
        let interner = LabelInterner::default();
        assert_eq!(None, interner.resolve(0));
        assert_eq!(None, interner.resolve(42));
    }

    #[test]
    fn round_trip_with_strings() {
        let mut interner = LabelInterner::default();
        let label = Label::from_str("hello").unwrap();
        let id = interner.get_or_intern(&label).unwrap();
        assert_eq!(Some("hello"), interner.resolve(id));
    }

    #[test]
    fn respects_capacity_limit() {
        let mut interner = LabelInterner {
            next: NextLabelId(LabelId::MAX),
            ..LabelInterner::default()
        };
        let label = Label::Alpha(123);
        assert!(matches!(
            interner.get_or_intern(&label),
            Err(LabelInternerError::CapacityExceeded)
        ));
    }

    #[test]
    fn canonicalizes_equivalent_texts() {
        let mut interner = LabelInterner::default();
        let padded = Label::Str(['f', 'o', 'o', ' ', ' ', ' ', ' ', ' ']);
        let trimmed = Label::from_str("foo").unwrap();
        let first = interner.get_or_intern(&padded).unwrap();
        let second = interner.get_or_intern(&trimmed).unwrap();
        assert_eq!(first, second);
    }

    #[test]
    fn reuses_identifiers_after_roundtrip() {
        let mut interner = LabelInterner::default();
        let label = Label::from_str("reuse").unwrap();
        let original = interner.get_or_intern(&label).unwrap();
        let serialized = serde::encode_to_vec(&interner, bincode::config::legacy()).unwrap();
        let mut restored: LabelInterner =
            serde::decode_from_slice(&serialized, bincode::config::legacy())
                .unwrap()
                .0;
        assert_eq!(Some(original), restored.get(&label));
        let reused = restored.get_or_intern(&label).unwrap();
        assert_eq!(original, reused);
    }
}
