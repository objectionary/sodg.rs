// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use std::fmt::{self, Debug, Display, Formatter};
use std::str::FromStr;

use anyhow::bail;
use rstest::rstest;

use crate::Label;

impl FromStr for Label {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(tail) = s.strip_prefix('α') {
            Ok(Self::Alpha(tail.parse::<usize>()?))
        } else if s.is_empty() {
            Ok(Self::Str([' '; 8]))
        } else {
            let mut chars = s.chars();
            let first = chars.next().unwrap();
            if chars.clone().next().is_none() {
                return Ok(Self::Greek(first));
            }
            let mut a: [char; 8] = [' '; 8];
            a[0] = first;
            for (i, c) in chars.enumerate() {
                let idx = i + 1;
                if idx >= a.len() {
                    bail!("Can't parse more than {} chars", a.len());
                }
                a[idx] = c;
            }
            Ok(Self::Str(a))
        }
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
            Self::Greek(c) => f.write_str(c.to_string().as_str()),
            Self::Alpha(i) => f.write_str(format!("α{i}").as_str()),
            Self::Str(a) => {
                f.write_str(a.iter().filter(|c| **c != ' ').collect::<String>().as_str())
            }
        }
    }
}

#[rstest]
#[case("𝜑")]
#[case("α5")]
#[case("hello")]
fn parses_and_prints(#[case] txt: &str) {
    let l = Label::from_str(txt).unwrap();
    assert_eq!(txt, l.to_string());
}

#[test]
fn parses_single_unicode_as_greek() {
    let label = Label::from_str("λ").unwrap();
    assert!(matches!(label, Label::Greek('λ')));
}
