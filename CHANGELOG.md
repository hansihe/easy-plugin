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
