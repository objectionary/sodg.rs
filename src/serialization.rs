// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use std::fs;
use std::path::Path;
use std::time::Instant;

use anyhow::{Context as _, Result};
use log::trace;

use crate::Sodg;

impl<const N: usize> Sodg<N> {
    fn rebuild_edge_indexes(&mut self) {
        let vertex_ids: Vec<usize> = self
            .vertices
            .iter()
            .map(|(vertex_id, _)| vertex_id)
            .collect();
        for vertex_id in vertex_ids {
            if let Some(vertex) = self.vertices.get_mut(vertex_id) {
                vertex.rebuild_index();
            }
        }
    }

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
        let mut sodg: Self = bincode::serde::decode_from_slice(&bytes, bincode::config::legacy())
            .with_context(|| format!("Can't deserialize from {}", path.display()))?
            .0;
        sodg.rebuild_edge_indexes();
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
    use std::convert::TryFrom as _;
    use std::str::FromStr as _;

    use tempfile::TempDir;

    use super::*;
    use crate::{EdgeIndex, Hex, Label, SMALL_THRESHOLD};

    #[test]
    fn can_save() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
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
        g.add(1);
        let label = Label::from_str("foo").unwrap();
        g.bind(0, 1, label).unwrap();
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("foo.sodg");
        g.save(file.as_path()).unwrap();
        let after: Sodg<1> = Sodg::load(file.as_path()).unwrap();
        assert_eq!(g.inspect(0).unwrap(), after.inspect(0).unwrap());
        assert_eq!(Some(1), after.kid(0, label));
        let kid = after.kids(0).next().unwrap();
        assert_eq!(label, *kid.label());
        assert_eq!(1, kid.destination());
    }

    #[test]
    fn rebuilds_indices_and_labels_after_roundtrip() {
        let mut g: Sodg<64> = Sodg::empty(512);
        g.add(0);
        g.add(1);
        g.add(2);
        for idx in 0..(SMALL_THRESHOLD + 3) {
            let destination = idx % 2 + 1;
            g.bind(0, destination, Label::Alpha(idx)).unwrap();
        }
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("roundtrip.sodg");
        g.save(file.as_path()).unwrap();
        let after: Sodg<64> = Sodg::load(file.as_path()).unwrap();
        let vertex = after.vertices.get(0).unwrap();
        assert!(matches!(vertex.index, EdgeIndex::Large(_)));
        assert_eq!(vertex.edges.len(), vertex.index.len());
        for edge in &vertex.edges {
            let encoded = u32::try_from(edge.to).expect("vertex identifier fits into u32");
            assert_eq!(Some(encoded), vertex.index.get(edge.label_id));
            let label_text = after.edge_label_text(edge);
            let parsed = Label::from_str(label_text.as_ref()).expect("edge label parsed");
            assert_eq!(edge.to, after.kid(0, parsed).expect("kid found after load"));
            assert_eq!(Some(edge.label_id), after.labels.get(&edge.label));
        }
    }
}
