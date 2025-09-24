// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use std::fmt::{self, Debug, Display, Formatter, Write as _};
use std::str::FromStr;

use anyhow::bail;
use rstest::rstest;

use crate::Label;

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
        let mut a: [char; 8] = [' '; 8];
        for (i, c) in s.chars().enumerate() {
            if i > 7 {
                bail!("Can't parse more than {} chars", a.len());
            }
            a[i] = c;
        }
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
                for c in a.iter().copied().filter(|c| *c != ' ') {
                    f.write_char(c)?;
                }
                Ok(())
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
fn parses_alpha_without_digits_as_greek() {
    assert_eq!(Label::Greek('α'), Label::from_str("α").unwrap());
}
