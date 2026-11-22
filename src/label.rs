// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::fmt::{self, Debug, Display, Formatter, Write as _};
use std::str::FromStr;

use anyhow::bail;
use rstest::rstest;

use crate::{LABEL_SIZE, Label};

impl FromStr for Label {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();
        if let Some(first) = chars.next() {
            if first == 'α' {
                let tail = chars.as_str();
                if tail.is_empty() {
                    return Ok(Self::Greek('α'));
                }
                return Ok(Self::Alpha(tail.parse::<usize>()?));
            }
            if chars.as_str().is_empty() {
                return Ok(Self::Greek(first));
            }
        }
        if s.is_empty() {
            bail!("Can't parse an empty label");
        }
        if s.contains('\0') {
            bail!("Can't parse a label with a NUL character: '{s}'");
        }
        let mut a = [0_u8; LABEL_SIZE];
        if s.len() > a.len() {
            bail!("Can't parse more than {} bytes in a label: '{s}'", a.len());
        }
        a[..s.len()].copy_from_slice(s.as_bytes());
        Ok(Self::Str(a))
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        <&Self as Debug>::fmt(&self, f)
    }
}

impl Debug for Label {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Self::Greek(c) => f.write_char(c),
            Self::Alpha(i) => {
                f.write_char('α')?;
                Display::fmt(&i, f)
            }
            Self::Str(a) => {
                let len = a.iter().position(|b| *b == 0).unwrap_or(a.len());
                let txt = std::str::from_utf8(&a[..len]).map_err(|_| fmt::Error)?;
                f.write_str(txt)
            }
        }
    }
}

#[rstest]
#[case("𝜑")]
#[case("α5")]
#[case("hello")]
#[case("as-number")]
#[case("привет-мир")]
#[case("abcdefghijklmnopqrstuvwxyz012345")]
fn parses_and_prints(#[case] txt: &str) {
    let l = Label::from_str(txt).unwrap();
    assert_eq!(txt, l.to_string());
}

#[test]
fn parses_alpha_without_digits_as_greek() {
    assert_eq!(Label::Greek('α'), Label::from_str("α").unwrap());
}

#[test]
fn rejects_too_long_label() {
    assert!(Label::from_str("abcdefghijklmnopqrstuvwxyz0123456").is_err());
}

#[test]
fn rejects_empty_label() {
    assert!(Label::from_str("").is_err());
}

#[test]
fn keeps_label_copy() {
    let l = Label::from_str("as-number").unwrap();
    let copy = l;
    assert_eq!(l, copy);
}
