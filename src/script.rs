// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::borrow::Cow;
use std::collections::HashMap;
use std::str::FromStr as _;

use anyhow::{Context as _, Result, bail};
use log::trace;

use crate::{Hex, Script};
use crate::{Label, Sodg};

impl Script {
    /// Make a new one, parsing a string with instructions, as printed
    /// by `phino sodg`.
    ///
    /// There must be one command per line: a letter and its arguments,
    /// separated by spaces. There are six commands possible:
    ///
    /// - `F o attr0 attr1 ...` calls [`Sodg::formation`],
    /// - `D o base attr` calls [`Sodg::dispatch`],
    /// - `A o proto attr arg` calls [`Sodg::application`],
    /// - `P o attr kid` calls [`Sodg::put`],
    /// - `Δ o data` calls [`Sodg::delta`], with data in `XX-XX-...` format,
    /// - `λ o name` calls [`Sodg::lambda`].
    ///
    /// A cell may either be a non-negative integer, which is used as is,
    /// or a name, like `c0`, which is replaced by a number from
    /// [`Sodg::next_id`] when it is seen for the first time.
    /// Everything after `#` till the end of the line is a comment.
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Script};
    /// use sodg::Sodg;
    ///
    /// let mut s = Script::from_str(
    ///   "F c0 foo\nF c1\nP c0 foo c1"
    /// );
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// let total = s.deploy_to(&mut g).unwrap();
    /// assert_eq!(3, total);
    /// assert_eq!(1, g.kid(0, Label::from_str("foo").unwrap()).unwrap());
    /// ```
    #[allow(clippy::should_implement_trait)]
    #[must_use]
    pub fn from_str(s: &str) -> Self {
        Self {
            txt: s.to_string(),
            vars: HashMap::new(),
        }
    }

    /// Deploy the entire script to the [`Sodg`], returning the number
    /// of commands deployed.
    ///
    /// # Errors
    ///
    /// If impossible to deploy, an error will be returned.
    pub fn deploy_to<const N: usize>(&mut self, g: &mut Sodg<N>) -> Result<usize> {
        let mut total = 0;
        for (idx, line) in self.txt.clone().lines().enumerate() {
            let cmd = line
                .split_once('#')
                .map_or(line, |(before, _)| before)
                .trim();
            if cmd.is_empty() {
                continue;
            }
            trace!("#deploy_to: deploying line no.{} '{}'...", idx + 1, cmd);
            self.deploy_one(cmd, g)
                .with_context(|| format!("Failure at the line no.{}: '{cmd}'", idx + 1))?;
            total += 1;
        }
        Ok(total)
    }

    /// Deploy a single command to the [`Sodg`].
    ///
    /// # Errors
    ///
    /// If impossible to deploy, an error will be returned.
    fn deploy_one<const N: usize>(&mut self, cmd: &str, g: &mut Sodg<N>) -> Result<()> {
        let mut parts = cmd.split_whitespace();
        let name = parts.next().context("Command is expected")?;
        let args: Vec<&str> = parts.collect();
        match name {
            "F" => {
                let (c, attrs) = args.split_first().context("Cell is expected")?;
                let c = self.parse(c, g)?;
                let attrs = attrs
                    .iter()
                    .map(|a| Self::parse_label(a))
                    .collect::<Result<Vec<Label>>>()?;
                g.formation(c, &attrs);
            }
            "D" => {
                Self::arity(name, &args, 3)?;
                let c = self.parse(args[0], g)?;
                let base = self.parse(args[1], g)?;
                let attr = Self::parse_label(args[2])?;
                g.dispatch(c, base, attr);
            }
            "A" => {
                Self::arity(name, &args, 4)?;
                let c = self.parse(args[0], g)?;
                let proto = self.parse(args[1], g)?;
                let attr = Self::parse_label(args[2])?;
                let arg = self.parse(args[3], g)?;
                g.application(c, proto, attr, arg);
            }
            "P" => {
                Self::arity(name, &args, 3)?;
                let c = self.parse(args[0], g)?;
                let attr = Self::parse_label(args[1])?;
                let kid = self.parse(args[2], g)?;
                g.put(c, attr, kid);
            }
            "Δ" => {
                Self::arity(name, &args, 2)?;
                let c = self.parse(args[0], g)?;
                let d = Self::parse_data(args[1])?;
                g.delta(c, &d);
            }
            "λ" => {
                Self::arity(name, &args, 2)?;
                let c = self.parse(args[0], g)?;
                g.lambda(c, args[1]);
            }
            other => {
                bail!("Unknown command: {other}");
            }
        }
        Ok(())
    }

    /// Make sure the command has exactly the expected number of arguments.
    ///
    /// # Errors
    ///
    /// If the number of arguments is wrong, an error will be returned.
    fn arity(name: &str, args: &[&str], expected: usize) -> Result<()> {
        if args.len() != expected {
            bail!(
                "The command '{name}' expects {expected} arguments, while {} provided",
                args.len()
            );
        }
        Ok(())
    }

    /// Parse a label of an attribute.
    ///
    /// # Errors
    ///
    /// If impossible to parse, an error will be returned.
    fn parse_label(s: &str) -> Result<Label> {
        Label::from_str(s).with_context(|| format!("Can't parse attribute '{s}'"))
    }

    /// Parse data.
    ///
    /// # Errors
    ///
    /// If impossible to parse, an error will be returned.
    fn parse_data(s: &str) -> Result<Hex> {
        let cleaned: Cow<'_, str> = if s
            .chars()
            .any(|c| matches!(c, ' ' | '\t' | '\n' | '\r' | '-'))
        {
            Cow::Owned(
                s.chars()
                    .filter(|c| !matches!(c, ' ' | '\t' | '\n' | '\r' | '-'))
                    .collect(),
            )
        } else {
            Cow::Borrowed(s)
        };
        if !cleaned.len().is_multiple_of(2) {
            bail!("Can't parse data '{s}': odd number of hexadecimal digits");
        }
        let mut bytes = Vec::with_capacity(cleaned.len() / 2);
        for (chunk_index, chunk) in cleaned.as_bytes().as_chunks::<2>().0.iter().enumerate() {
            let byte = Self::parse_hex_pair(chunk).with_context(|| {
                let pos = chunk_index * 2;
                format!("Can't parse data '{s}' at position {pos}")
            })?;
            bytes.push(byte);
        }
        Ok(Hex::from_vec(bytes))
    }

    /// Parse `42` into `42`, and a name, like `c0`, into the number
    /// assigned to it when it was seen for the first time.
    ///
    /// # Errors
    ///
    /// If impossible to parse, an error will be returned.
    fn parse<const N: usize>(&mut self, s: &str, g: &mut Sodg<N>) -> Result<usize> {
        if s.is_empty() {
            bail!("Empty identifier");
        }
        if s.chars().all(|c| c.is_ascii_digit()) {
            return usize::from_str(s).with_context(|| format!("Parsing of '{s}' failed"));
        }
        if let Some(c) = self.vars.get(s) {
            return Ok(*c);
        }
        let c = g.next_id();
        self.vars.insert(s.to_string(), c);
        Ok(c)
    }

    fn parse_hex_pair(pair: &[u8]) -> Result<u8> {
        let high = Self::parse_hex_digit(pair[0])
            .with_context(|| format!("Invalid hexadecimal digit '{}'", char::from(pair[0])))?;
        let low = Self::parse_hex_digit(pair[1])
            .with_context(|| format!("Invalid hexadecimal digit '{}'", char::from(pair[1])))?;
        Ok((high << 4) | low)
    }

    const fn parse_hex_digit(digit: u8) -> Option<u8> {
        match digit {
            b'0'..=b'9' => Some(digit - b'0'),
            b'a'..=b'f' => Some(digit - b'a' + 10),
            b'A'..=b'F' => Some(digit - b'A' + 10),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Kind;

    fn label(s: &str) -> Label {
        Label::from_str(s).unwrap()
    }

    const PHINO: &str = "F c0 foo bar
F c1 x y
F c2
Δ c2 2A-
P c1 x c2
D c3 c0 bar
D c4 c1 x
A c5 c3 z c4
D c6 c5 t
P c1 y c6
λ c1 L_foo
P c0 foo c1
F c7 z t
D c8 c7 ρ
D c9 c8 z
P c7 t c9
P c0 bar c7
";

    #[test]
    fn deploys_output_of_phino() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let total = Script::from_str(PHINO).deploy_to(&mut g).unwrap();
        assert_eq!(17, total);
        assert_eq!(10, g.len());
        let pi = Label::Greek('π');
        assert_eq!(Kind::Formation, g.kind(0));
        assert_eq!(&[label("foo"), label("bar")], g.attrs(0));
        assert_eq!(1, g.kid(0, label("foo")).unwrap());
        assert_eq!(7, g.kid(0, label("bar")).unwrap());
        assert_eq!(&[label("x"), label("y")], g.attrs(1));
        assert_eq!(2, g.kid(1, label("x")).unwrap());
        assert_eq!(6, g.kid(1, label("y")).unwrap());
        assert_eq!(Some("L_foo"), g.atom(1));
        assert_eq!(Kind::Formation, g.kind(2));
        assert_eq!(0, g.attrs(2).len());
        assert_eq!(Kind::Dispatch(label("bar")), g.kind(3));
        assert_eq!(0, g.kid(3, pi).unwrap());
        assert_eq!(Kind::Dispatch(label("x")), g.kind(4));
        assert_eq!(1, g.kid(4, pi).unwrap());
        assert_eq!(Kind::Application(label("z")), g.kind(5));
        assert_eq!(3, g.kid(5, pi).unwrap());
        assert_eq!(4, g.kid(5, label("z")).unwrap());
        assert_eq!(Kind::Dispatch(label("t")), g.kind(6));
        assert_eq!(5, g.kid(6, pi).unwrap());
        assert_eq!(&[label("z"), label("t")], g.attrs(7));
        assert!(g.kid(7, label("z")).is_none());
        assert_eq!(9, g.kid(7, label("t")).unwrap());
        assert_eq!(Kind::Dispatch(label("ρ")), g.kind(8));
        assert_eq!(7, g.kid(8, pi).unwrap());
        assert_eq!(Kind::Dispatch(label("z")), g.kind(9));
        assert_eq!(8, g.kid(9, pi).unwrap());
        assert_eq!(&[0x2A], g.data(2).unwrap().bytes());
    }

    #[test]
    fn deploys_with_comments_and_blank_lines() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let mut s = Script::from_str(
            "
            # a formation with one attribute
            F c0 foo
            F c1   # an empty one
            Δ c1 d0-bf-D1-80-d0-B8-d0-b2-d0-b5-d1-82
            P c0 foo c1
            ",
        );
        let total = s.deploy_to(&mut g).unwrap();
        assert_eq!(4, total);
        assert_eq!(1, g.kid(0, label("foo")).unwrap());
        assert_eq!("привет", g.data(1).unwrap().to_utf8().unwrap());
    }

    #[test]
    fn deploys_long_attributes() {
        let mut g: Sodg<16> = Sodg::empty(256);
        Script::from_str("F c0 as-number\nF c1\nD c2 c1 as-number\nP c0 as-number c2")
            .deploy_to(&mut g)
            .unwrap();
        assert_eq!(&[label("as-number")], g.attrs(0));
        assert_eq!(Kind::Dispatch(label("as-number")), g.kind(2));
        assert_eq!(2, g.kid(0, label("as-number")).unwrap());
    }

    #[test]
    fn deploys_numeric_cells() {
        let mut g: Sodg<16> = Sodg::empty(256);
        Script::from_str("F 5 x\nF 7\nP 5 x 7")
            .deploy_to(&mut g)
            .unwrap();
        assert_eq!(7, g.kid(5, label("x")).unwrap());
    }

    #[test]
    fn deploys_empty_data() {
        let mut g: Sodg<16> = Sodg::empty(256);
        Script::from_str("F c0\nΔ c0 --").deploy_to(&mut g).unwrap();
        assert!(g.data(0).unwrap().is_empty());
    }

    #[test]
    fn trailing_comment_without_newline() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let mut s = Script::from_str("F c0\n# trailing comment");
        let total = s.deploy_to(&mut g).unwrap();
        assert_eq!(1, total);
    }

    #[test]
    fn rejects_unknown_command() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let err = Script::from_str("F c0\nADD(0);")
            .deploy_to(&mut g)
            .unwrap_err();
        assert!(format!("{err:#}").contains("line no.2"), "{err:#}");
    }

    #[test]
    fn rejects_wrong_arity() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let err = Script::from_str("F c0\nF c1\nP c0 foo")
            .deploy_to(&mut g)
            .unwrap_err();
        let msg = format!("{err:#}");
        assert!(msg.contains("expects 3 arguments"), "{msg}");
        assert!(msg.contains("P c0 foo"), "{msg}");
    }

    #[test]
    fn parse_data_supports_mixed_formatting() {
        let hex = Script::parse_data("FF-00 0A\n0B").unwrap();
        assert_eq!(hex.bytes(), &[0xFF, 0x00, 0x0A, 0x0B]);
    }

    #[test]
    fn parse_data_rejects_invalid_digit() {
        assert!(Script::parse_data("ZZ").is_err());
    }
}
