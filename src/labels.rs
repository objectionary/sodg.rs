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
use std::hash::BuildHasherDefault;
use std::str::{FromStr as _, Utf8Error};

use std::borrow::Cow;

use itoa::Buffer as UsizeBuffer;
use rustc_hash::FxHasher;
use serde::de::value::SeqAccessDeserializer;
use serde::{
    Deserialize, Deserializer, Serialize, Serializer, de::SeqAccess, ser::SerializeStruct,
};
use smallvec::SmallVec;

use crate::Label;

/// Identifier of an interned label.
pub type LabelId = u32;

const INLINE_LABEL_KEY_CAPACITY: usize = 32;

/// Errors that may occur while working with a [`LabelInterner`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LabelInternerError {
    /// The number of unique labels exceeded the representable [`LabelId`] range.
    CapacityExceeded,
    /// The label contains a character that cannot be represented canonically.
    InvalidLabelCharacter(char),
}

impl Display for LabelInternerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::CapacityExceeded => f.write_str("label pool exhausted"),
            Self::InvalidLabelCharacter(ch) => {
                write!(f, "label contains unsupported character '{ch}'")
            }
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
#[derive(Debug, Default, Clone)]
pub struct LabelInterner {
    forward: HashMap<LabelKey, LabelId, BuildHasherDefault<FxHasher>>,
    reverse: Vec<Box<str>>,
    canonical: Vec<Label>,
    next: NextLabelId,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
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
    /// Returns [`LabelInternerError::InvalidLabelCharacter`] when the
    /// corresponding [`Label::Str`] contains a non-ASCII character.
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
        let key = LabelKey::from_label(label)?;
        if let Some(id) = self.forward.get(&key).copied() {
            return Ok(id);
        }
        let owned = key.clone_into_boxed_str();
        let canonical = Self::canonicalize_label(label)?;
        let id = self.next.allocate()?;
        let offset = id
            .checked_sub(1)
            .ok_or(LabelInternerError::CapacityExceeded)?;
        let index = usize::try_from(offset).map_err(|_| LabelInternerError::CapacityExceeded)?;
        if self.reverse.len() != index {
            debug_assert!(
                false,
                "reverse table length must equal next identifier offset"
            );
            return Err(LabelInternerError::CapacityExceeded);
        }
        self.reverse.push(owned);
        self.canonical.push(canonical);
        self.forward.insert(key, id);
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
        let key = LabelKey::from_label(label).ok()?;
        self.forward.get(&key).copied()
    }

    /// Retrieve the identifier previously assigned to [`label`](Label) without
    /// mutating the interner.
    ///
    /// The method is intentionally equivalent to [`get`](Self::get) but keeps
    /// semantic clarity when callers specifically need to access a cached
    /// identifier. It returns [`None`] if the label was not interned yet.
    ///
    /// # Examples
    ///
    /// ```
    /// use sodg::{Label, LabelInterner};
    ///
    /// let mut interner = LabelInterner::default();
    /// let label = Label::Alpha(1);
    /// let id = interner.get_or_intern(&label).unwrap();
    /// assert_eq!(Some(id), interner.lookup(&label));
    /// assert!(interner.lookup(&Label::Alpha(99)).is_none());
    /// ```
    #[must_use]
    pub fn lookup(&self, label: &Label) -> Option<LabelId> {
        self.get(label)
    }

    /// Derive the canonical UTF-8 representation of the provided [`Label`].
    ///
    /// The returned value matches the representation stored inside the
    /// [`LabelInterner`] when the label is interned. Callers can use this helper
    /// to sanitize labels obtained from external sources before comparing them
    /// against interned identifiers.
    ///
    /// # Errors
    ///
    /// Returns [`LabelInternerError::InvalidLabelCharacter`] when the label
    /// contains a non-ASCII character that cannot participate in the canonical
    /// UTF-8 representation.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// # use std::str::FromStr as _;
    /// # use sodg::{Label, LabelInterner};
    /// let canonical = LabelInterner::canonicalize(&Label::from_str("foo bar").unwrap()).unwrap();
    /// assert_eq!(Label::from_str("foobar").unwrap(), canonical);
    /// ```
    pub(crate) fn canonicalize(label: &Label) -> Result<Label, LabelInternerError> {
        Self::canonicalize_label(label)
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
    #[must_use]
    pub fn resolve(&self, id: LabelId) -> Option<&str> {
        if id == 0 {
            return None;
        }
        let offset = id.checked_sub(1)?;
        let index = usize::try_from(offset).ok()?;
        self.reverse.get(index).map(std::convert::AsRef::as_ref)
    }

    /// Retrieve the canonical [`Label`] associated with the identifier.
    ///
    /// Returns [`None`] if the identifier is zero or has not been interned.
    #[must_use]
    pub fn canonical_label(&self, id: LabelId) -> Option<&Label> {
        if id == 0 {
            return None;
        }
        let offset = id.checked_sub(1)?;
        let index = usize::try_from(offset).ok()?;
        self.canonical.get(index)
    }

    fn canonicalize_label(label: &Label) -> Result<Label, LabelInternerError> {
        match label {
            Label::Greek(symbol) => Ok(Label::Greek(*symbol)),
            Label::Alpha(index) => Ok(Label::Alpha(*index)),
            Label::Str(chars) => {
                let mut canonical = [' '; 8];
                let mut position = 0_usize;
                for &symbol in chars {
                    if symbol == ' ' {
                        continue;
                    }
                    if !symbol.is_ascii() {
                        return Err(LabelInternerError::InvalidLabelCharacter(symbol));
                    }
                    if position >= canonical.len() {
                        break;
                    }
                    canonical[position] = symbol;
                    position += 1;
                }
                Ok(Label::Str(canonical))
            }
        }
    }

    fn ensure_invariants(&self) -> Result<(), String> {
        let next = usize::try_from(self.next.0)
            .map_err(|_| "label identifier exceeds usize range".to_owned())?;
        if next == 0 {
            return Err("next identifier must remain non-zero".into());
        }
        let expected_len = next.saturating_sub(1);
        if expected_len != self.reverse.len() {
            return Err("reverse table length does not match next id".into());
        }
        if expected_len != self.canonical.len() {
            return Err("canonical label table length does not match next id".into());
        }
        if self.forward.len() != self.reverse.len() {
            return Err("forward map size does not match reverse table".into());
        }
        if self.reverse.len() != self.canonical.len() {
            return Err("reverse and canonical tables length mismatch".into());
        }
        let mut seen = vec![false; self.reverse.len()];
        for (key, id) in &self.forward {
            if *id == 0 {
                return Err("identifier zero is reserved".into());
            }
            let offset = id
                .checked_sub(1)
                .ok_or_else(|| "label identifier underflow".to_owned())?;
            let index = usize::try_from(offset)
                .map_err(|_| "label identifier exceeds usize range".to_owned())?;
            let entry = self
                .reverse
                .get(index)
                .ok_or_else(|| "identifier does not have reverse entry".to_owned())?;
            let expected = key
                .canonical_text()
                .map_err(|_| "label key is not valid UTF-8".to_owned())?;
            let expected = expected.into_owned();
            if entry.as_ref() != expected {
                return Err("forward and reverse entries mismatch".into());
            }
            let canonical = self
                .canonical
                .get(index)
                .ok_or_else(|| "missing canonical label".to_owned())?;
            if canonical.to_string() != expected {
                return Err("canonical label does not match stored text".into());
            }
            if seen[index] {
                return Err("duplicate identifier present".into());
            }
            seen[index] = true;
        }
        if seen.iter().any(|value| !value) {
            return Err("reverse table contains entries without forward keys".into());
        }
        Ok(())
    }
}

impl Serialize for LabelInterner {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[cfg(debug_assertions)]
        self.ensure_invariants()
            .map_err(serde::ser::Error::custom)?;
        let mut state = serializer.serialize_struct("LabelInterner", 4)?;
        state.serialize_field("forward", &self.forward)?;
        state.serialize_field("reverse", &self.reverse)?;
        state.serialize_field("canonical", &self.canonical)?;
        state.serialize_field("next", &self.next)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for LabelInterner {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct LabelInternerSerde {
            forward: HashMap<LabelKey, LabelId, BuildHasherDefault<FxHasher>>,
            reverse: Vec<Box<str>>,
            #[serde(default)]
            canonical: Vec<Label>,
            #[serde(default)]
            next: NextLabelId,
        }

        let LabelInternerSerde {
            forward,
            reverse,
            canonical,
            next,
        } = LabelInternerSerde::deserialize(deserializer)?;
        let canonical = if canonical.is_empty() && !reverse.is_empty() {
            let mut restored = Vec::with_capacity(reverse.len());
            for text in &reverse {
                let label = Label::from_str(text)
                    .map_err(|error| serde::de::Error::custom(error.to_string()))?;
                restored.push(label);
            }
            restored
        } else {
            canonical
        };
        let interner = Self {
            forward,
            reverse,
            canonical,
            next,
        };
        interner
            .ensure_invariants()
            .map_err(serde::de::Error::custom)?;
        Ok(interner)
    }
}

/// Owned canonical label key used as a hash-map entry.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LabelKey {
    Alpha(usize),
    Greek(char),
    Str(SmallVec<[u8; INLINE_LABEL_KEY_CAPACITY]>),
}

impl LabelKey {
    fn from_label(label: &Label) -> Result<Self, LabelInternerError> {
        match label {
            Label::Greek(symbol) => Ok(Self::Greek(*symbol)),
            Label::Alpha(index) => Ok(Self::Alpha(*index)),
            Label::Str(chars) => Self::from_char_slice(chars),
        }
    }

    fn from_char_slice(chars: &[char; 8]) -> Result<Self, LabelInternerError> {
        let mut bytes = SmallVec::<[u8; INLINE_LABEL_KEY_CAPACITY]>::new();
        for &symbol in chars {
            if symbol == ' ' {
                continue;
            }
            if !symbol.is_ascii() {
                return Err(LabelInternerError::InvalidLabelCharacter(symbol));
            }
            bytes.push(symbol as u8);
        }
        Ok(Self::Str(bytes))
    }

    fn canonical_text(&self) -> Result<Cow<'_, str>, Utf8Error> {
        match self {
            Self::Greek(symbol) => {
                let mut encoded = [0_u8; 4];
                let text = symbol.encode_utf8(&mut encoded);
                Ok(Cow::Owned(text.to_owned()))
            }
            Self::Alpha(index) => {
                let mut formatter = UsizeBuffer::new();
                let digits = formatter.format(*index);
                let mut text = String::with_capacity(1 + digits.len());
                text.push('α');
                text.push_str(digits);
                Ok(Cow::Owned(text))
            }
            Self::Str(bytes) => Ok(Cow::Borrowed(std::str::from_utf8(bytes)?)),
        }
    }

    fn clone_into_boxed_str(&self) -> Box<str> {
        #[cfg(test)]
        {
            LABEL_KEY_CLONE_CALLS.with(|counter| counter.set(counter.get() + 1));
        }
        match self {
            Self::Greek(symbol) => {
                let mut encoded = [0_u8; 4];
                symbol.encode_utf8(&mut encoded).to_owned().into_boxed_str()
            }
            Self::Alpha(index) => {
                let mut formatter = UsizeBuffer::new();
                let digits = formatter.format(*index);
                let mut text = String::with_capacity(1 + digits.len());
                text.push('α');
                text.push_str(digits);
                text.into_boxed_str()
            }
            Self::Str(bytes) => match String::from_utf8(bytes.clone().into_vec()) {
                Ok(text) => text.into_boxed_str(),
                Err(error) => {
                    debug_assert!(false, "label keys must remain valid UTF-8");
                    String::from_utf8_lossy(&error.into_bytes())
                        .into_owned()
                        .into_boxed_str()
                }
            },
        }
    }

    #[cfg(test)]
    fn as_string(&self) -> String {
        match self.canonical_text() {
            Ok(Cow::Borrowed(text)) => text.to_owned(),
            Ok(Cow::Owned(text)) => text,
            Err(_) => panic!("label keys must remain valid UTF-8"),
        }
    }
}

impl Serialize for LabelKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let text = self
            .canonical_text()
            .map_err(|error| <S::Error as serde::ser::Error>::custom(error.to_string()))?;
        match text {
            Cow::Borrowed(value) => serializer.serialize_str(value),
            Cow::Owned(value) => serializer.serialize_str(value.as_str()),
        }
    }
}

impl<'de> Deserialize<'de> for LabelKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        fn from_text<E>(text: &str) -> Result<LabelKey, E>
        where
            E: serde::de::Error,
        {
            let label = Label::from_str(text)
                .map_err(|error| <E as serde::de::Error>::custom(error.to_string()))?;
            LabelKey::from_label(&label)
                .map_err(|error| <E as serde::de::Error>::custom(error.to_string()))
        }

        fn from_bytes<E>(bytes: &[u8]) -> Result<LabelKey, E>
        where
            E: serde::de::Error,
        {
            let text = std::str::from_utf8(bytes)
                .map_err(|error| <E as serde::de::Error>::custom(error.to_string()))?;
            from_text(text)
        }

        struct LabelKeyVisitor;

        impl<'de> serde::de::Visitor<'de> for LabelKeyVisitor {
            type Value = LabelKey;

            fn expecting(&self, formatter: &mut Formatter<'_>) -> FmtResult {
                formatter.write_str("canonical label bytes or string")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                from_text(value)
            }

            fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                from_text(&value)
            }

            fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                from_bytes(value)
            }

            fn visit_borrowed_bytes<E>(self, value: &'de [u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                from_bytes(value)
            }

            fn visit_byte_buf<E>(self, value: Vec<u8>) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                from_bytes(&value)
            }

            fn visit_seq<A>(self, seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let bytes: Vec<u8> = Deserialize::deserialize(SeqAccessDeserializer::new(seq))?;
                from_bytes(&bytes)
            }
        }

        if deserializer.is_human_readable() {
            deserializer.deserialize_str(LabelKeyVisitor)
        } else {
            deserializer.deserialize_bytes(LabelKeyVisitor)
        }
    }
}

#[cfg(test)]
thread_local! {
    static LABEL_KEY_CLONE_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn reset_label_key_clone_counter() {
    LABEL_KEY_CLONE_CALLS.with(|counter| counter.set(0));
}

#[cfg(test)]
fn label_key_clone_calls() -> usize {
    LABEL_KEY_CLONE_CALLS.with(|counter| counter.get())
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use bincode::serde;

    use super::*;

    #[test]
    fn builds_greek_label_key() {
        let label = Label::Greek('λ');
        let key = LabelKey::from_label(&label).unwrap();
        assert_eq!("λ", key.as_string());
    }

    #[test]
    fn builds_alpha_label_key() {
        let label = Label::Alpha(42);
        let key = LabelKey::from_label(&label).unwrap();
        assert_eq!("α42", key.as_string());
    }

    #[test]
    fn trims_string_labels_in_key() {
        let label = Label::Str(['f', 'o', 'o', ' ', ' ', 'b', 'a', 'r']);
        let key = LabelKey::from_label(&label).unwrap();
        assert_eq!("foobar", key.as_string());
    }

    #[test]
    fn lookup_returns_identifier_without_mutation() {
        let mut interner = LabelInterner::default();
        let label = Label::Alpha(3);
        assert!(interner.lookup(&label).is_none());
        let id = interner.get_or_intern(&label).unwrap();
        assert_eq!(Some(id), interner.lookup(&label));
    }

    #[test]
    fn rejects_non_ascii_string_label() {
        let label = Label::Str(['α', ' ', ' ', ' ', ' ', ' ', ' ', ' ']);
        let result = LabelKey::from_label(&label);
        assert!(matches!(
            result,
            Err(LabelInternerError::InvalidLabelCharacter('α'))
        ));
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
        reset_label_key_clone_counter();
        let mut interner = LabelInterner::default();
        let label = Label::Alpha(7);
        interner.get_or_intern(&label).unwrap();
        let after_first = label_key_clone_calls();
        assert_eq!(1, after_first);
        interner.get_or_intern(&label).unwrap();
        let after_second = label_key_clone_calls();
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

    #[test]
    fn canonical_label_returns_structured_variant() {
        let mut interner = LabelInterner::default();
        let original = Label::Str(['f', 'o', 'o', ' ', ' ', ' ', ' ', ' ']);
        let id = interner.get_or_intern(&original).unwrap();
        let canonical = interner.canonical_label(id).copied();
        assert_eq!(Some(Label::from_str("foo").unwrap()), canonical);
    }

    #[test]
    fn canonical_label_is_none_for_unknown_identifier() {
        let interner = LabelInterner::default();
        assert!(interner.canonical_label(0).is_none());
        assert!(interner.canonical_label(42).is_none());
    }
}
