// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::fs;
use std::path::Path;
use std::time::Instant;

use anyhow::{Context as _, Result};
use log::trace;

use crate::Sodg;

impl<const N: usize> Sodg<N> {
    /// Save the entire [`Sodg`] into a binary file.
    ///
    /// The entire [`Sodg`] can be restored from the file.
    /// The function returns the size of the file just saved. In order
    /// to restore from the file, use [`Sodg::load`].
    ///
    /// # Errors
    ///
    /// If impossible to save, an error will be returned.
    pub fn save(&self, path: &Path) -> Result<usize> {
        let start = Instant::now();
        let bytes: Vec<u8> = bincode::serde::encode_to_vec(self, bincode::config::legacy())
            .context("Failed to serialize")?;
        let size = bytes.len();
        fs::write(path, bytes).with_context(|| format!("Can't write to {}", path.display()))?;
        trace!(
            "Serialized {} vertices ({} bytes) to {} in {:?}",
            self.len(),
            size,
            path.display(),
            start.elapsed(),
        );
        Ok(size)
    }

    /// Load the entire [`Sodg`] from a binary file previously
    /// created by [`Sodg::save`].
    ///
    /// # Errors
    ///
    /// If impossible to load, an error will be returned.
    pub fn load(path: &Path) -> Result<Self> {
        let start = Instant::now();
        let bytes =
            fs::read(path).with_context(|| format!("Can't read from {}", path.display()))?;
        let size = bytes.len();
        let sodg: Self = bincode::serde::decode_from_slice(&bytes, bincode::config::legacy())
            .with_context(|| format!("Can't deserialize from {}", path.display()))?
            .0;
        trace!(
            "Deserialized {} vertices ({} bytes) from {} in {:?}",
            sodg.len(),
            size,
            path.display(),
            start.elapsed()
        );
        Ok(sodg)
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use tempfile::TempDir;

    use super::*;
    use crate::{Hex, Label};

    #[test]
    fn can_save() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap());
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("foo.sodg");
        g.save(file.as_path()).unwrap();
        assert!(file.metadata().unwrap().len() > 0);
    }

    #[test]
    fn saves_and_loads() {
        let mut g: Sodg<1> = Sodg::empty(100);
        g.add(0);
        g.put(0, &Hex::from_str_bytes("hello"));
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("foo.sodg");
        g.save(file.as_path()).unwrap();
        let after: Sodg<1> = Sodg::load(file.as_path()).unwrap();
        assert_eq!(g.inspect(0).unwrap(), after.inspect(0).unwrap());
    }
}
