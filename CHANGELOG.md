## [0.11.0] - 2016-10-02

### Added
- Added structured argument specifications

### Changed
- Changed enumerated argument specifications to be defined outside other argument specifications

### Fixed
- Fixed code generation for nested sequences with different amounts
- Fixed partial parsing of sequences and enumerated specifiers

## [0.10.0] - 2016-09-22

### Removed
- Removed `easy_plugin` enum variant

### Added
- Added `parse_specification_string` function

### Changed
- Renamed `convert` module to `extractor`
- Renamed `parse_args` function to `parse_arguments`
- Renamed `parse_spec` function to `parse_specification`
- Refactored arguments and specifications

## [0.9.1] - 2016-08-17

### Fixed
- Updated for latest nightly

## [0.9.0] - 2016-08-17

### Added
- Added `convert` specifiers

## [0.8.1] - 2016-08-15

### Fixed
- Updated for latest nightly

## [0.8.0] - 2016-07-28

### Changed
- Added support for the stable and beta Rust channels

## [0.7.3] - 2016-7-19

### Fixed
- Updated for latest nightly

## [0.7.2] - 2016-7-17

### Fixed
- Updated for latest nightly

## [0.7.1] - 2016-7-11

### Fixed
- Updated for latest nightly

## [0.7.0] - 2016-7-4

### Fixed
- Updated for latest nightly

## [0.6.2] - 2016-6-23

### Fixed
- Updated for latest nightly

## [0.6.1] - 2016-6-10

### Fixed
- Updated for latest nightly

## [0.6.0] - 2016-5-28

### Changed
- Renamed `parse_specification` plugin to `parse_spec`
- Renamed `parse_arguments` function to `parse_args`

### Fixed
- Updated for latest nightly

## [0.5.0] - 2016-5-15

### Added
- Added `PluginResultExt` trait
- Added `ToError` trait

### Changed
- Changed `convert` module `TokenTree` function interfaces

## [0.4.0] - 2016-5-13

### Added
- Added `convert` module

### Fixed
- Improved generated spans

### Changed
- Changed `path` storage type to `Path`

## [0.3.4] - 2016-5-7

### Fixed
- Updated for latest nightly

## [0.3.3] - 2016-4-28

### Fixed
- Updated for latest nightly

## [0.3.2] - 2016-4-8

### Fixed
- Updated for latest nightly

## [0.3.1] - 2016-4-5

### Changed
- Implemented `Clone` and `Debug` for argument enums and structs

## [0.3.0] - 2016-4-2

### Added
- Added `Specification` struct

### Changed
- Wrapped `binop`, `delim`, `ident`, `lftm`, `path`, `tok`, and named sequence values in
  `syntax::codemap::Spanned`

## [0.2.10] - 2016-4-1

### Fixed
- Improved error reporting

## [0.2.9] - 2016-3-16

### Fixed
- Improved error reporting

## [0.2.8] - 2016-3-13

### Fixed
- Fixed spurious `unexpected end of arguments` error with sequences

## [0.2.7] - 2016-3-5

### Fixed
- Updated for latest nightly

## [0.2.6] - 2016-2-14

### Fixed
- Updated for latest nightly

## [0.2.5] - 2016-2-5

### Fixed
- Updated for latest nightly

## [0.2.4] - 2016-1-12

### Fixed
- Updated for latest nightly

## [0.2.3] - 2016-1-2

### Fixed
- Updated for latest nightly

## [0.2.2] - 2015-12-21

### Fixed
- Updated for latest nightly

## [0.2.1] - 2015-12-05

### Fixed
- Fixed error spans for plugins supplied with zero arguments

## [0.2.0] - 2015-12-04

### Added
- Added support for sequences with zero or one repetitions (`$(sequence)?`)
- Added support for named sequences

### Fixed
- Fixed overeager sequence parsing

## [0.1.2] - 2015-12-01

### Fixed
- Updated for latest nightly

## [0.1.1] - 2015-11-15

### Fixed
- Updated for latest nightly

## [0.1.0] - 2015-11-12
- Initial release
