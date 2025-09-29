// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::VecDeque;
use std::str::FromStr;

use anyhow::{bail, Context as _, Result};

use crate::{Label, Sodg};

const MAX_FIND_RECURSION: usize = 128;

impl<const N: usize> Sodg<N> {
    /// Locate a vertex starting from `start` by following the dot-separated `locator`.
    ///
    /// The path segments are interpreted as edge labels. When a segment can't be
    /// resolved directly, the provided `resolver` is invoked with the current
    /// vertex identifier and the missing attribute. The resolver must return an
    /// alternative locator that will be followed recursively. Returning an empty
    /// locator keeps the traversal at the current vertex. Locators starting with
    /// `"ν"` are treated as absolute vertex identifiers.
    ///
    /// # Errors
    ///
    /// Returns an error when:
    ///
    /// * Any vertex along the path does not exist or is not alive.
    /// * A path segment cannot be parsed into a [`Label`].
    /// * The `resolver` closure returns an error.
    /// * The recursive resolution exceeds `MAX_FIND_RECURSION`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Label, Sodg};
    ///
    /// let mut g: Sodg<16> = Sodg::empty(256);
    /// g.add(0);
    /// g.add(1);
    /// g.bind(0, 1, Label::from_str("foo")?)?;
    /// let found = g.find_with_closure(0, "foo", |_v, _a| Ok(String::new()))?;
    /// assert_eq!(1, found);
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn find_with_closure<F>(
        &self,
        start: usize,
        locator: &str,
        mut resolver: F,
    ) -> Result<usize>
    where
        F: FnMut(usize, &str) -> Result<String>,
    {
        self.find_with_closure_recursive(start, locator, &mut resolver, 0)
    }

    fn find_with_closure_recursive<F>(
        &self,
        start: usize,
        locator: &str,
        resolver: &mut F,
        depth: usize,
    ) -> Result<usize>
    where
        F: FnMut(usize, &str) -> Result<String>,
    {
        if depth >= MAX_FIND_RECURSION {
            bail!(
                "Recursion depth limit ({MAX_FIND_RECURSION}) exceeded while resolving '{locator}' from ν{start}"
            );
        }
        self.ensure_vertex_alive(start)?;
        let mut vertex = start;
        let mut segments: VecDeque<String> = locator
            .split('.')
            .filter(|segment| !segment.is_empty())
            .map(ToOwned::to_owned)
            .collect();

        while let Some(segment) = segments.pop_front() {
            // Absolute jump: segment like "ν123"
            if let Some(rest) = segment.strip_prefix('ν') {
                let id = rest
                    .parse::<usize>()
                    .with_context(|| format!("Can't parse vertex identifier from '{segment}'"))?;
                self.ensure_vertex_alive(id)?;
                vertex = id;
                continue;
            }

            // Normal step by label
            let current = vertex;
            let label = Label::from_str(segment.as_str())
                .with_context(|| format!("Can't parse label '{segment}'"))?;

            if let Some(next) = self.kid(current, label) {
                self.ensure_vertex_alive(next)?;
                vertex = next;
                continue;
            }

            // Try alternative path from resolver
            let alternative = resolver(current, segment.as_str()).with_context(|| {
                format!("Resolver failed to provide alternative for ν{current}.{segment}")
            })?;
            vertex = self
                .find_with_closure_recursive(current, alternative.as_str(), resolver, depth + 1)
                .with_context(|| {
                    format!(
                        "Alternative path '{alternative}' from ν{current}.{segment} did not resolve"
                    )
                })?;
        }
        Ok(vertex)
    }

    fn ensure_vertex_alive(&self, id: usize) -> Result<()> {
        let vertex = self
            .vertices
            .get(id)
            .with_context(|| format!("Can't find ν{id}"))?;
        if vertex.branch == 0 {
            bail!("Can't find ν{id}");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_vertex_via_resolver() -> anyhow::Result<()> {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.add(3);
        g.bind(1, 2, Label::from_str("first")?)?;
        g.bind(2, 3, Label::from_str("alt")?)?;
        let found = g.find_with_closure(1, "first.second", |v, a| {
            if v == 2 && a == "second" {
                Ok("alt".to_string())
            } else {
                Ok(String::new())
            }
        })?;
        assert_eq!(3, found);
        Ok(())
    }

    #[test]
    fn returns_start_for_empty_locator() -> anyhow::Result<()> {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(5);
        let found = g.find_with_closure(5, "", |_v, _a| Ok(String::new()))?;
        assert_eq!(5, found);
        Ok(())
    }

    #[test]
    fn redirects_through_sub_locator() -> anyhow::Result<()> {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(1);
        g.add(2);
        g.bind(1, 2, Label::from_str("xyz")?)?;
        g.add(3);
        g.bind(2, 3, Label::from_str("x")?)?;
        let found = g.find_with_closure(1, "a.x", |v, a| {
            if v == 1 && a == "a" {
                Ok("xyz".to_string())
            } else {
                Ok(String::new())
            }
        })?;
        assert_eq!(3, found);
        Ok(())
    }

    #[test]
    fn jumps_to_absolute_vertex() -> anyhow::Result<()> {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo")?)?;
        let found = g.find_with_closure(0, "bar", |_v, _a| Ok("ν1".to_string()))?;
        assert_eq!(1, found);
        Ok(())
    }

    #[test]
    fn propagates_resolver_error() -> anyhow::Result<()> {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        let result = g.find_with_closure(0, "bar", |_v, _a| anyhow::bail!("no alternative"));
        assert!(result.is_err());
        let err = result.err().unwrap();
        let has_cause = err
            .chain()
            .any(|cause| cause.to_string().contains("no alternative"));
        assert!(has_cause, "{}", err);
        Ok(())
    }

    #[test]
    fn guards_against_recursion_overflow() -> anyhow::Result<()> {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        let result = g.find_with_closure(0, "foo", |_v, _a| Ok("foo".to_string()));
        assert!(result.is_err());
        let err = result.err().unwrap();
        let has_depth_note = err
            .chain()
            .any(|cause| cause.to_string().contains("Recursion depth"));
        assert!(has_depth_note, "{}", err);
        Ok(())
    }
}

