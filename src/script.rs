// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::HashMap;
use std::str::FromStr as _;
use std::sync::LazyLock as Lazy;

use anyhow::{Context as _, Result, bail};
use log::trace;
use regex::Regex;

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
        for cmd in &self.commands() {
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
        static LINE: Lazy<Regex> = Lazy::new(|| Regex::new("^([A-Z]+) *\\(([^)]*)\\)$").unwrap());
        let cap = LINE
            .captures(cmd)
            .with_context(|| format!("Can't parse '{cmd}'"))?;
        let args: Vec<String> = cap[2]
            .split(',')
            .map(str::trim)
            .filter(|t| !t.is_empty())
            .map(ToString::to_string)
            .collect();
        match &cap[1] {
            "ADD" => {
                let v = self.parse(args.first().context("V is expected")?, g)?;
                g.add(v);
            }
            "BIND" => {
                let v1 = self.parse(args.first().context("V1 is expected")?, g)?;
                let v2 = self.parse(args.get(1).context("V2 is expected")?, g)?;
                let a = Label::from_str(args.get(2).context("Label is expected")?.as_str())?;
                g.bind(v1, v2, a);
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
        static DATA_STRIP: Lazy<Regex> = Lazy::new(|| Regex::new("[ \t\n\r\\-]").unwrap());
        static DATA: Lazy<Regex> =
            Lazy::new(|| Regex::new("^[0-9A-Fa-f]{2}([0-9A-Fa-f]{2})*$").unwrap());
        let d: &str = &DATA_STRIP.replace_all(s, "");
        if !DATA.is_match(d) {
            bail!("Can't parse data '{s}'");
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
}
