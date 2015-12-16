# Change Log

All notable changes to this project will be documented in this file.
This project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

### Added

- `combinators::bounded::many`: combinator applying a parser within a range bound, storing the data
  in a `T: FromIterator`.
- `combinators::bounded::skip_many`: combinator applying a parser within a range bound, throwing
  away all produced data.
- `combinators::bounded::many_till`: combinator applying a parser within a range bound until a
  second parser succeeds. If the second parser does not succeed within the given range the parsing
  will fail. The matches from the first parser will be stored in a `T: FromIterator`.

### Changes

- `count`, `many1`, `sep_by1` now properly uses `Iterator::size_hint`
- **Backwards-incompatible:** `many`, `many1`, `sep_by`, `sep_by1`, `skip_many`, `skip_many1` are
  no longer considered incomplete if they end with a partial match as long as they have managed to
  satisfy the minimum count of matches.
- **Backwards-incompatible:** `buffer::ParseError` has been renamed to `buffer::StreamError` to not
  conflict with the simple `ParseError`.
- Slightly improved performance for `count`, `many`, `many1`, `sep_by`, `sep_by1`.

## [0.1.2] - 2015-12-02

### Added

- `ascii::digit`
- `ascii::is_end_of_line`
- `ascii::is_horizontal_space`
- `ascii::signed`
- `ascii::skip_whitespace`
- `combinators::look_ahead`
- `combinators::many_till`
- `combinators::matched_by`
- `combinators::sep_by1`
- `combinators::sep_by`
- `combinators::skip_many1`
- `parsers::peek_next`
- `parsers::run_scanner`
- `parsers::satisfy_with`

## [0.1.1] - 2015-11-28

### Added

- `parsers::Error::new`, useful for creating error values of unknown type.

## [0.1.0] - 2015-11-24

Initial release.
