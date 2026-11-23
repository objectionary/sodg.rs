// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::collections::VecDeque;
use std::str::FromStr;

use anyhow::{Context as _, Result, bail};

use crate::{Label, Sodg};

const MAX_FIND_RECURSION: usize = 128;

impl<const N: usize> Sodg<N> {
    /// Locate a cell starting from `start` by following the dot-separated `locator`.
    ///
    /// The path segments are interpreted as edge labels. When a segment can't be
    /// resolved directly, the provided `resolver` is invoked with the current
    /// cell identifier and the missing attribute. The resolver must return an
    /// alternative locator that will be followed recursively. Returning an empty
    /// locator keeps the traversal at the current cell. Locators starting with
    /// `"ν"` are treated as absolute cell identifiers.
    ///
    /// # Errors
    ///
    /// * Returns an error if any of the cells along the path is absent.
    /// * Returns an error if a label segment can't be parsed into a [`Label`].
    /// * Propagates any error raised by the resolver closure.
    /// * Returns an error if recursion depth exceeds the internal recursion limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::str::FromStr as _;
    ///
    /// use sodg::{Label, Sodg};
    ///
    /// let mut g: Sodg<16> = Sodg::empty(256);
    /// g.formation(0, &[]);
    /// g.formation(1, &[]);
    /// g.put(0, Label::from_str("foo").unwrap(), 1);
    /// let found = g
    ///     .find_with_closure(0, "foo", |_v, _a| Ok(String::new()))
    ///     .unwrap();
    /// assert_eq!(1, found);
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
        if depth > MAX_FIND_RECURSION {
            bail!(
                "Recursion depth limit ({MAX_FIND_RECURSION}) exceeded while resolving '{locator}' from c{start}"
            );
        }
        self.ensure_cell_alive(start)?;
        let mut cell = start;
        let mut segments: VecDeque<String> = locator
            .split('.')
            .filter(|segment| !segment.is_empty())
            .map(ToOwned::to_owned)
            .collect();
        while let Some(segment) = segments.pop_front() {
            if let Some(rest) = segment.strip_prefix('ν') {
                let id = rest
                    .parse::<usize>()
                    .with_context(|| format!("Can't parse cell identifier from '{segment}'"))?;
                self.ensure_cell_alive(id)?;
                cell = id;
                continue;
            }
            let current = cell;
            let label = Label::from_str(segment.as_str())
                .with_context(|| format!("Can't parse label '{segment}'"))?;
            let target = {
                let cell = self
                    .cells
                    .get(current)
                    .with_context(|| format!("Can't find c{current}"))?;
                if !cell.made {
                    bail!("Can't find c{current}");
                }
                cell.edges
                    .iter()
                    .find(|(edge_label, _)| **edge_label == label)
                    .map(|(_, to)| *to)
            };
            if let Some(next) = target {
                self.ensure_cell_alive(next)?;
                cell = next;
                continue;
            }
            let alternative = resolver(current, segment.as_str()).with_context(|| {
                format!("Resolver failed to provide alternative for c{current}.{segment}")
            })?;
            cell = self
                .find_with_closure_recursive(current, alternative.as_str(), resolver, depth + 1)
                .with_context(|| {
                    format!(
                        "Alternative path '{alternative}' from c{current}.{segment} did not resolve"
                    )
                })?;
        }
        Ok(cell)
    }

    fn ensure_cell_alive(&self, id: usize) -> Result<()> {
        let cell = self
            .cells
            .get(id)
            .with_context(|| format!("Can't find c{id}"))?;
        if !cell.made {
            bail!("Can't find c{id}");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::Label;

    #[test]
    fn finds_cell_via_resolver() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.formation(3, &[]);
        g.put(1, Label::from_str("first").unwrap(), 2);
        g.put(2, Label::from_str("alt").unwrap(), 3);
        let found = g
            .find_with_closure(1, "first.second", |v, a| {
                if v == 2 && a == "second" {
                    Ok("alt".to_string())
                } else {
                    Ok(String::new())
                }
            })
            .unwrap();
        assert_eq!(3, found);
    }

    #[test]
    fn returns_start_for_empty_locator() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(5, &[]);
        let found = g
            .find_with_closure(5, "", |_v, _a| Ok(String::new()))
            .unwrap();
        assert_eq!(5, found);
    }

    #[test]
    fn redirects_through_sub_locator() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.put(1, Label::from_str("xyz").unwrap(), 2);
        g.formation(3, &[]);
        g.put(2, Label::from_str("x").unwrap(), 3);
        let found = g
            .find_with_closure(1, "a.x", |v, a| {
                if v == 1 && a == "a" {
                    Ok("xyz".to_string())
                } else {
                    Ok(String::new())
                }
            })
            .unwrap();
        assert_eq!(3, found);
    }

    #[test]
    fn jumps_to_absolute_cell() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        g.formation(1, &[]);
        g.put(0, Label::from_str("foo").unwrap(), 1);
        let found = g
            .find_with_closure(0, "bar", |_v, _a| Ok("ν1".to_string()))
            .unwrap();
        assert_eq!(1, found);
    }

    #[test]
    fn propagates_resolver_error() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        let result = g.find_with_closure(0, "bar", |_v, _a| anyhow::bail!("no alternative"));
        assert!(result.is_err());
        let err = result.err().unwrap();
        let has_cause = err
            .chain()
            .any(|cause| cause.to_string().contains("no alternative"));
        assert!(has_cause, "{}", err);
    }

    #[test]
    fn guards_against_recursion_overflow() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        let result = g.find_with_closure(0, "foo", |_v, _a| Ok("foo".to_string()));
        assert!(result.is_err());
        let err = result.err().unwrap();
        let has_depth_note = err
            .chain()
            .any(|cause| cause.to_string().contains("Recursion depth"));
        assert!(has_depth_note, "{}", err);
    }

    #[test]
    fn errors_when_start_cell_is_missing() {
        let g: Sodg<16> = Sodg::empty(256);
        let result = g.find_with_closure(7, "foo", |_v, _a| Ok(String::new()));
        assert!(result.is_err());
        let err = result.err().unwrap();
        let mentions_missing = err.chain().any(|cause| cause.to_string().contains("c7"));
        assert!(mentions_missing, "{}", err);
    }

    #[test]
    fn errors_when_absolute_segment_is_not_numeric() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        let result = g.find_with_closure(0, "νabc", |_v, _a| Ok(String::new()));
        assert!(result.is_err());
        let err = result.err().unwrap();
        let mentions_segment = err.chain().any(|cause| cause.to_string().contains("νabc"));
        assert!(mentions_segment, "{}", err);
    }

    #[test]
    fn errors_when_absolute_jump_targets_missing_cell() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        let result = g.find_with_closure(0, "ν9", |_v, _a| Ok(String::new()));
        assert!(result.is_err());
        let err = result.err().unwrap();
        let mentions_target = err.chain().any(|cause| cause.to_string().contains("c9"));
        assert!(mentions_target, "{}", err);
    }

    #[test]
    fn errors_when_label_segment_is_too_long() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(0, &[]);
        let too_long = "abcdefghijklmnopqrstuvwxyz0123456";
        let result = g.find_with_closure(0, too_long, |_v, _a| Ok(String::new()));
        assert!(result.is_err());
        let err = result.err().unwrap();
        let mentions_label = err
            .chain()
            .any(|cause| cause.to_string().contains(too_long));
        assert!(mentions_label, "{}", err);
    }
}
