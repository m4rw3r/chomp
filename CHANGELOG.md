# Change Log

All notable changes to this project will be documented in this file.
This project adheres to [Semantic Versioning](http://semver.org/).

## [0.2.6] - 2016-07-07

### Bugfixes

- Macro expansion is now again compatible with nightly.

## [0.2.5] - 2016-03-08

### Added

- `combinators::bounded::sep_by`: Bounded version of `combinators::sep_by` and `combinators::sep_by1`.

### Changes

- Improved performance of combinators using iterators.
- Updated bitflags dependency

## [0.2.4] - 2016-01-24

### Changes

- **Backwards-incompatible:** `combinators::option` will now return the default value if the
  parser reports incomplete and the input is finite.

## [0.2.3] - 2016-01-21

### Added

- `buffer::StreamError` now implements `From<ParseError>`

### Changes

- **Backwards-incompatible:** `combinators::or` will now retry with the second parser if the
  first parser reports incomplete and the input is finite.
- Improvements to `parse!` macro to make it more general and to make it easier to write simple
  parsers as one line. Completely updated grammar and reimplemented the macro to include:

   * Alternation operator (`<|>`)
   * Skip operator (`<*`)
   * Then operator (`>>`)
   * `ret` and `err` can now be used inline
   * **Backwards-incompatible:** `;` is no longer allowed to terminate a `parse!` block.

## [0.2.2] - 2016-01-13

### Changes

* `Input::ret`, `ParseResult::bind` and `ParseResult::then` no longer have type parameter
  defaults. This change only affects people on nightly who have `type-parameter-defaults`
  enabled. See Rust [pull request #30724](https://github.com/rust-lang/rust/pull/30724).

## [0.2.1] - 2015-12-20

### Changes

* `buffer::GrowingBuffer` and `buffer::data_source::ReadDataSource` now derive `Debug`.
* Rustdoc for public items previously lacking any documentation.

## [0.2.0] - 2015-12-16

### Added

- `parse_only`: Runs a given parser on a finite input.
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

### Deprecated

- `Input::new`

  Use `parse_only` or `buffer::SliceStream` to parse a slice instead. For any advanced usage create
  an `Input` using `primitives::input::new`.

- `ParseResult::unwrap`, `ParseResult::unwrap_err`, `ParseResult::expect`

  Use `parse_only` or the `buffer::Stream` implementations to obtain a `Result` instead of acting
  on the `ParseResult` directly.

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
