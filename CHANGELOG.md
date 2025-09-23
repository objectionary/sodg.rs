# Changelog

## [0.0.2] - 2025-09-23

### Changed

- Formatted the changelog to comply with markdownlint requirements.

## [0.0.1] - 2025-09-23

### Changed

- Prevented padding zero bytes when promoting short `Hex::Bytes`
  concatenations to `Vec` storage so that previously stored payload is
  preserved during overflow handling.

### Added

- Added a regression test covering concatenation of `Hex::Bytes` with a
  long `Hex::Vector` to ensure no spurious zeros appear between operands.

### Maintenance

- Bumped the crate version to `0.0.1` to publish the concatenation fix.
