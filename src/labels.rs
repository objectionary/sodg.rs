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
use std::fmt::{Display, Formatter, Result as FmtResult, Write as _};
use std::hash::BuildHasherDefault;

use arrayvec::ArrayString;
use rustc_hash::FxHasher;
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
    forward: HashMap<String, LabelId, BuildHasherDefault<FxHasher>>,
    reverse: HashMap<LabelId, String, BuildHasherDefault<FxHasher>>,
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
        let key = CanonicalLabel::from_label(label);
        if let Some(id) = self.forward.get(key.as_str()) {
            return Ok(*id);
        }
        let id = self.next.allocate()?;
        let owned = key.into_owned();
        self.forward.insert(owned.clone(), id);
        self.reverse.insert(id, owned);
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
        let key = CanonicalLabel::from_label(label);
        self.forward.get(key.as_str()).copied()
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

const INLINE_CANONICAL_CAPACITY: usize = 32;

#[derive(Debug, Clone)]
enum CanonicalLabel {
    Inline(ArrayString<INLINE_CANONICAL_CAPACITY>),
    Owned(String),
}

impl CanonicalLabel {
    fn from_label(label: &Label) -> Self {
        match label {
            Label::Greek(symbol) => Self::from_char(*symbol),
            Label::Alpha(index) => Self::from_alpha(*index),
            Label::Str(chars) => Self::from_char_slice(chars),
        }
    }

    fn from_char(symbol: char) -> Self {
        let mut inline = ArrayString::<INLINE_CANONICAL_CAPACITY>::new();
        match inline.try_push(symbol) {
            Ok(()) => Self::Inline(inline),
            Err(_) => Self::Owned(symbol.to_string()),
        }
    }

    fn from_alpha(index: usize) -> Self {
        let mut inline = ArrayString::<INLINE_CANONICAL_CAPACITY>::new();
        if inline.try_push('α').is_err() {
            return Self::Owned(format!("α{index}"));
        }
        match write!(&mut inline, "{index}") {
            Ok(()) => Self::Inline(inline),
            Err(_) => Self::Owned(format!("α{index}")),
        }
    }

    fn from_char_slice(chars: &[char; 8]) -> Self {
        let mut inline = ArrayString::<INLINE_CANONICAL_CAPACITY>::new();
        for symbol in chars {
            if *symbol == ' ' {
                continue;
            }
            if inline.try_push(*symbol).is_err() {
                return Self::Owned(chars.iter().filter(|ch| **ch != ' ').collect::<String>());
            }
        }
        Self::Inline(inline)
    }

    fn as_str(&self) -> &str {
        match self {
            Self::Inline(buffer) => buffer.as_str(),
            Self::Owned(text) => text.as_str(),
        }
    }

    fn into_owned(self) -> String {
        #[cfg(test)]
        {
            CANONICAL_INTO_OWNED.with(|counter| counter.set(counter.get() + 1));
        }
        match self {
            Self::Inline(buffer) => buffer.as_str().to_owned(),
            Self::Owned(text) => text,
        }
    }
}

#[cfg(test)]
thread_local! {
    static CANONICAL_INTO_OWNED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn reset_canonical_into_owned_counter() {
    CANONICAL_INTO_OWNED.with(|counter| counter.set(0));
}

#[cfg(test)]
fn canonical_into_owned_calls() -> usize {
    CANONICAL_INTO_OWNED.with(|counter| counter.get())
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use bincode::serde;

    use super::*;

    #[test]
    fn canonicalizes_greek_inline() {
        let label = Label::Greek('λ');
        let canonical = CanonicalLabel::from_label(&label);
        match canonical {
            CanonicalLabel::Inline(ref inline) => assert_eq!("λ", inline.as_str()),
            CanonicalLabel::Owned(_) => panic!("expected inline canonical form"),
        }
        assert_eq!("λ", canonical.as_str());
    }

    #[test]
    fn canonicalizes_alpha_inline() {
        let label = Label::Alpha(42);
        let canonical = CanonicalLabel::from_label(&label);
        match canonical {
            CanonicalLabel::Inline(ref inline) => assert_eq!("α42", inline.as_str()),
            CanonicalLabel::Owned(_) => panic!("expected inline canonical form"),
        }
        assert_eq!("α42", canonical.as_str());
    }

    #[test]
    fn canonicalizes_and_trims_string_labels() {
        let label = Label::Str(['f', 'o', 'o', ' ', ' ', 'b', 'a', 'r']);
        let canonical = CanonicalLabel::from_label(&label);
        assert_eq!("foobar", canonical.as_str());
    }

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
    fn repeated_interning_does_not_reallocate() {
        reset_canonical_into_owned_counter();
        let mut interner = LabelInterner::default();
        let label = Label::Alpha(7);
        interner.get_or_intern(&label).unwrap();
        let after_first = canonical_into_owned_calls();
        assert_eq!(1, after_first);
        interner.get_or_intern(&label).unwrap();
        let after_second = canonical_into_owned_calls();
        assert_eq!(after_first, after_second);
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
