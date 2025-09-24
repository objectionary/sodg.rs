# Changelog

## [0.0.3] - 2025-09-23

### Fixed (0.0.3)

- Treated `Label::from_str("α")` as `Label::Greek('α')` to avoid parsing an empty
  suffix while preserving existing `αN` parsing.

### Added (0.0.3)

- Introduced a regression test ensuring the bare alpha label maps to the Greek
  variant.

## [0.0.2] - 2025-09-23

### Changed (0.0.2)

- Formatted the changelog to comply with markdownlint requirements.

## [0.0.1] - 2025-09-23

### Changed (0.0.1)

- Prevented padding zero bytes when promoting short `Hex::Bytes`
  concatenations to `Vec` storage so that previously stored payload is
  preserved during overflow handling.

### Added

- Added a regression test covering concatenation of `Hex::Bytes` with a
  long `Hex::Vector` to ensure no spurious zeros appear between operands.

### Maintenance

- Bumped the crate version to `0.0.1` to publish the concatenation fix.
