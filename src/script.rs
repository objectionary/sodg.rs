// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use std::borrow::Cow;
use std::collections::HashMap;
use std::str::FromStr as _;

use anyhow::{Context as _, Result, bail};
use log::trace;

use crate::{Hex, Script};
use crate::{Label, Sodg};

impl Script {
    /// Make a new one, parsing a string with instructions.
    ///
    /// Instructions
    /// must be separated by semicolon. There are just three of them
    /// possible: `ADD`, `BIND`, and `PUT`. The arguments must be
    /// separated by a comma. An argument may either be 1) a positive integer
    /// (possibly prepended by `ν`),
    /// 2) a variable started with `$`, 3) an attribute name, or
    /// 4) data in `XX-XX-...` hexadecimal format.
    ///
    /// For example:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Script};
    /// use sodg::Sodg;
    ///
    /// let mut s = Script::from_str(
    ///   "ADD(0); ADD($ν1); BIND(ν0, $ν1, foo);"
    /// );
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// let total = s.deploy_to(&mut g).unwrap();
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

    /// Deploy the entire script to the [`Sodg`].
    ///
    /// # Errors
    ///
    /// If impossible to deploy, an error will be returned.
    pub fn deploy_to<const N: usize>(&mut self, g: &mut Sodg<N>) -> Result<usize> {
        self.vars.clear();
        let mut pos = 0;
        for cmd in commands.split(';').map(str::trim).filter(|t| !t.is_empty()) {
            trace!("#deploy_to: deploying command no.{} '{}'...", pos + 1, cmd);
            self.deploy_one(cmd, g)
                .with_context(|| format!("Failure at the command no.{pos}: '{cmd}'"))?;
            pos += 1;
        }
        Ok(pos)
    }

    /// Get all commands.
    fn commands(&self) -> Vec<String> {
        static STRIP_COMMENTS: Lazy<Regex> = Lazy::new(|| Regex::new(r"#.*(?:\r?\n|$)").unwrap());
        let text = self.txt.as_str();
        let clean: &str = &STRIP_COMMENTS.replace_all(text, "");
        clean
            .split(';')
            .map(str::trim)
            .filter(|t| !t.is_empty())
            .map(ToString::to_string)
            .collect()

    }

    /// Deploy a single command to the [`Sodg`].
    ///
    /// # Errors
    ///
    /// If impossible to deploy, an error will be returned.
    fn deploy_one<const N: usize>(&mut self, cmd: &str, g: &mut Sodg<N>) -> Result<()> {
        let (name, rest) = cmd
            .split_once('(')
            .with_context(|| format!("Can't parse '{cmd}'"))?;
        let trimmed_name = name.trim();
        let arguments = rest
            .rfind(')')
            .map(|idx| &rest[..idx])
            .context("Missing closing parenthesis")?;
        let args: Vec<String> = arguments
            .split(',')
            .map(str::trim)
            .filter(|t| !t.is_empty())
            .map(ToString::to_string)
            .collect();
        match trimmed_name {
            "ADD" => {
                let v = self.parse(args.first().context("V is expected")?, g)?;
                g.add(v);
            }
            "BIND" => {
                let v1 = self.parse(args.first().context("V1 is expected")?, g)?;
                let v2 = self.parse(args.get(1).context("V2 is expected")?, g)?;
                let a = Label::from_str(args.get(2).context("Label is expected")?.as_str())?;
                g.bind(v1, v2, a).unwrap();
            }
            "PUT" => {
                let v = self.parse(args.first().context("V is expected")?, g)?;
                let d = Self::parse_data(args.get(1).context("Data is expected")?)?;
                g.put(v, &d);
            }
            cmd => {
                bail!("Unknown command: {cmd}");
            }
        }
        Ok(())
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
        for (chunk_index, chunk) in cleaned.as_bytes().chunks_exact(2).enumerate() {
            let byte = Self::parse_hex_pair(chunk).with_context(|| {
                let pos = chunk_index * 2;
                format!("Can't parse data '{s}' at position {pos}")
            })?;
            bytes.push(byte);
        }
        let mut bytes = Vec::with_capacity(d.len() / 2);
        for i in (0..d.len()).step_by(2) {
            let pair = &d[i..i + 2];
            let byte = u8::from_str_radix(pair, 16)
                .with_context(|| format!("Can't parse data '{s}', invalid byte '{pair}'"))?;
            bytes.push(byte);
        }
        Ok(Hex::from_vec(bytes))
    }

    /// Parse `$ν5` into `5`, and `ν23` into `23`, and `42` into `42`.
    ///
    /// # Errors
    ///
    /// If impossible to parse, an error will be returned.
    fn parse<const N: usize>(&mut self, s: &str, g: &mut Sodg<N>) -> Result<usize> {
        let head = s.chars().next().context("Empty identifier")?;
        if head == '$' || head == 'ν' {
            let tail = s
                .get(head.len_utf8()..)
                .context("Identifier is missing a numeric suffix")?;
            if head == '$' {
                Ok(*self
                    .vars
                    .entry(tail.to_owned())
                    .or_insert_with(|| g.next_id()))
            } else {
                Ok(usize::from_str(tail).with_context(|| format!("Parsing of '{s}' failed"))?)
            }
        } else {
            let v = usize::from_str(s).with_context(|| format!("Parsing of '{s}' failed"))?;
            Ok(v)
        }
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

    #[test]
    fn simple_command() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let mut s = Script::from_str(
            "
            ADD(0);  ADD($ν1); # adding two vertices
            BIND(ν0, $ν1, foo  );
            PUT($ν1  , d0-bf-D1-80-d0-B8-d0-b2-d0-b5-d1-82);
            ",
        );
        let total = s.deploy_to(&mut g).unwrap();
        assert_eq!(4, total);
        let label = Label::from_str("foo").unwrap();
        assert_eq!(1, g.kid(0, label.clone()).unwrap());
        assert_eq!("привет", g.data(1).unwrap().to_utf8().unwrap());
        assert!(g.kid(0, label).is_none());
    }

    #[test]
    fn ignores_trailing_line_comment_without_newline() {
        let mut g: Sodg<16> = Sodg::empty(16);
        let mut script = Script::from_str("ADD(0);\n# trailing comment");
        let deployed = script.deploy_to(&mut g).unwrap();
        assert_eq!(1, deployed);
        assert!(g.data(0).is_none());
    }

    #[test]
    fn ignores_inline_trailing_comment_without_newline() {
        let mut g: Sodg<16> = Sodg::empty(16);
        let mut script = Script::from_str("ADD(0); # trailing comment");
        let deployed = script.deploy_to(&mut g).unwrap();
        assert_eq!(1, deployed);
        assert!(g.data(0).is_none());
    }

    #[test]
    fn resets_variables_between_deployments() {
        let mut g: Sodg<16> = Sodg::empty(16);
        let mut script = Script::from_str("ADD(0); ADD($ν1);");
        script.deploy_to(&mut g).unwrap();
        let initial_len = g.len();
        script.deploy_to(&mut g).unwrap();
        assert_eq!(initial_len + 1, g.len());
        assert!(g.keys().contains(&2));
    }

    #[test]
    fn trailing_comment_without_newline() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let mut s = Script::from_str("ADD(0);\n# trailing comment");
        let total = s.deploy_to(&mut g).unwrap();
        assert_eq!(1, total);
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

    #[test]
    fn strip_comments_removes_entire_comment_line() {
        let cleaned = Script::strip_comments("ADD(0);\n# comment\nADD(1);");
        assert_eq!(cleaned, "ADD(0);\nADD(1);");
    }
}
