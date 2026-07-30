// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use std::fs;
use std::mem::size_of;
use std::path::Path;
use std::time::Instant;

use anyhow::{Context as _, Result, bail};
use log::trace;

use crate::Sodg;

/// The first bytes of every file written by [`Sodg::save`].
const MAGIC: [u8; 4] = *b"SODG";

/// The revision of the binary layout that [`Sodg::save`] writes.
///
/// The encoding is [`bincode`] in its legacy configuration, which is not
/// self-describing: a file of one layout decoded as another either fails
/// somewhere in the middle or, worse, succeeds against misaligned bytes.
/// Revision one is the first one to carry this header at all, so a file
/// written before it is rejected by its missing [`MAGIC`] rather than
/// misread.
const VERSION: u32 = 1;

/// How many bytes [`MAGIC`] and [`VERSION`] take together.
const HEADER: usize = MAGIC.len() + size_of::<u32>();

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
        let mut bytes = Vec::with_capacity(HEADER);
        bytes.extend_from_slice(&MAGIC);
        bytes.extend_from_slice(&VERSION.to_le_bytes());
        bytes.extend(
            bincode::serde::encode_to_vec(self, bincode::config::legacy())
                .context("Failed to serialize")?,
        );
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
    /// If impossible to load, an error will be returned. A file written by a
    /// version of this crate that predates the interning of edge labels is
    /// rejected here, by its missing header, instead of being decoded into
    /// something else.
    pub fn load(path: &Path) -> Result<Self> {
        let start = Instant::now();
        let bytes =
            fs::read(path).with_context(|| format!("Can't read from {}", path.display()))?;
        let size = bytes.len();
        let payload = Self::payload_of(&bytes)
            .with_context(|| format!("Can't read the header of {}", path.display()))?;
        let sodg: Self = bincode::serde::decode_from_slice(payload, bincode::config::legacy())
            .with_context(|| format!("Can't deserialize from {}", path.display()))?
            .0;
        sodg.validate_labels()
            .with_context(|| format!("Can't trust the graph in {}", path.display()))?;
        trace!(
            "Deserialized {} vertices ({} bytes) from {} in {:?}",
            sodg.len(),
            size,
            path.display(),
            start.elapsed()
        );
        Ok(sodg)
    }

    /// Check the header of a saved file and return the bytes of the graph.
    fn payload_of(bytes: &[u8]) -> Result<&[u8]> {
        let Some((header, payload)) = bytes.split_at_checked(HEADER) else {
            bail!(
                "The file is {} bytes long, too short to hold even the {HEADER}-byte header of a SODG file",
                bytes.len()
            );
        };
        let (magic, version) = header.split_at(MAGIC.len());
        if magic != MAGIC {
            bail!(
                "This is not a SODG file: it does not start with 'SODG'; a file written before the format was tagged, i.e. before edge labels were interned, can't be read by this version"
            );
        }
        let version = u32::from_le_bytes(
            version
                .try_into()
                .expect("The header is longer than the magic by exactly four bytes"),
        );
        if version != VERSION {
            bail!("SODG format version {version} can't be read, {VERSION} is expected");
        }
        Ok(payload)
    }

    /// Check that every edge carries a label identifier this graph can resolve.
    ///
    /// [`Sodg::kids`] resolves identifiers without checking, because every
    /// identifier that [`Sodg::bind`] writes into a vertex was handed out by
    /// the interner of the same graph. A graph that arrives through [`serde`]
    /// carries no such guarantee: a truncated, hand-edited or foreign file
    /// decodes into a graph whose first read would abort the process. The
    /// check costs one pass over the edges, once, against an unbounded number
    /// of reads afterwards.
    fn validate_labels(&self) -> Result<()> {
        for (v, vtx) in self.vertices.iter() {
            for (label, to) in vtx.edges.iter() {
                if self.labels.resolve_ref(label).is_none() {
                    bail!(
                        "The edge ν{v} → ν{to} carries label #{label}, which this graph never interned"
                    );
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use tempfile::TempDir;

    use super::*;
    use crate::edge_index::EdgeIndex;
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
    fn saves_and_loads_edges_with_their_labels() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.add(2);
        g.bind(0, 1, Label::from_str("foo").unwrap());
        g.bind(0, 2, Label::Alpha(7));
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("foo.sodg");
        g.save(file.as_path()).unwrap();
        let after: Sodg<16> = Sodg::load(file.as_path()).unwrap();
        assert_eq!(
            Some(1),
            after.kid(0, Label::from_str("foo").unwrap()),
            "the textual label did not survive the round trip"
        );
        assert_eq!(
            Some(2),
            after.kid(0, Label::Alpha(7)),
            "the alpha label did not survive the round trip"
        );
        assert_eq!(g.to_xml().unwrap(), after.to_xml().unwrap());
    }

    #[test]
    fn saves_and_loads_a_vertex_that_outgrew_the_flat_index() {
        let mut g: Sodg<2> = Sodg::empty(256);
        g.add(0);
        for i in 1..=4 {
            g.add(i);
            g.bind(0, i, Label::Alpha(i));
        }
        assert!(
            matches!(g.vertices.get(0).unwrap().edges, EdgeIndex::Large(_)),
            "the test is pointless unless the vertex is hashed"
        );
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("large.sodg");
        g.save(file.as_path()).unwrap();
        let after: Sodg<2> = Sodg::load(file.as_path()).unwrap();
        assert!(
            matches!(after.vertices.get(0).unwrap().edges, EdgeIndex::Large(_)),
            "the hashed shape did not survive the round trip"
        );
        for i in 1..=4 {
            assert_eq!(Some(i), after.kid(0, Label::Alpha(i)));
        }
        assert_eq!(g.to_xml().unwrap(), after.to_xml().unwrap());
    }

    #[test]
    fn rejects_a_file_without_a_header() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("old.sodg");
        let bytes = bincode::serde::encode_to_vec(&g, bincode::config::legacy()).unwrap();
        fs::write(file.as_path(), bytes).unwrap();
        let error = Sodg::<16>::load(file.as_path()).unwrap_err();
        assert!(
            format!("{error:#}").contains("not a SODG file"),
            "{error:#}"
        );
    }

    #[test]
    fn rejects_a_file_shorter_than_the_header() {
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("tiny.sodg");
        fs::write(file.as_path(), b"SOD").unwrap();
        let error = Sodg::<16>::load(file.as_path()).unwrap_err();
        assert!(format!("{error:#}").contains("too short"), "{error:#}");
    }

    #[test]
    fn rejects_a_format_version_it_does_not_know() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("future.sodg");
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&MAGIC);
        bytes.extend_from_slice(&42_u32.to_le_bytes());
        bytes.extend(bincode::serde::encode_to_vec(&g, bincode::config::legacy()).unwrap());
        fs::write(file.as_path(), bytes).unwrap();
        let error = Sodg::<16>::load(file.as_path()).unwrap_err();
        assert!(format!("{error:#}").contains("version 42"), "{error:#}");
    }

    #[test]
    fn rejects_an_edge_whose_label_was_never_interned() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.add(1);
        g.bind(0, 1, Label::Alpha(0));
        g.vertices.get_mut(0).unwrap().edges.insert(999, 1);
        let tmp = TempDir::new().unwrap();
        let file = tmp.path().join("broken.sodg");
        g.save(file.as_path()).unwrap();
        let error = Sodg::<16>::load(file.as_path()).unwrap_err();
        assert!(format!("{error:#}").contains("#999"), "{error:#}");
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
