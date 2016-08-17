//! Bounded versions of combinators.
//!
//! This module provides bounded versions of `many`, `many_till` and `skip_many`.
//!
//! The core range types are used to describe a half-open range of successive applications of a
//! parser. `usize` is used to specify an exact number of iterations:
//!
//! ```
//! use chomp::combinators::bounded::many;
//! use chomp::parse_only;
//! use chomp::parsers::any;
//!
//! // Read any character 2 or 3 times
//! let r: Result<Vec<_>, _> = parse_only(|i| many(i, 2..4, any), b"abcd");
//!
//! assert_eq!(r, Ok(vec![b'a', b'b', b'c']));
//! ```

use std::marker::PhantomData;
use std::iter::FromIterator;
use std::ops::{
    Range,
    RangeFrom,
    RangeFull,
    RangeTo,
};
use std::cmp::max;

use types::{Input, ParseResult};
use primitives::{Primitives, IntoInner};

/// Trait for applying a parser multiple times based on a range.
pub trait BoundedRange {
    // TODO: Update documentation regarding input state. Incomplete will point to the last
    // successful parsed data. mark a backtrack point to be able to restart parsing.
    /// Applies the parser `F` multiple times until it fails or the maximum value of the range has
    /// been reached, collecting the successful values into a `T: FromIterator`.
    ///
    /// Propagates errors if the minimum number of iterations has not been met
    ///
    /// # Panics
    ///
    /// Will panic if the end of the range is smaller than the start of the range.
    ///
    /// # Notes
    ///
    /// * Will allocate depending on the `FromIterator` implementation.
    /// * Must never yield more items than the upper bound of the range.
    /// * Use `combinators::bounded::many` instead of calling this trait method directly.
    /// * If the last parser succeeds on the last input item then this parser is still considered
    ///   incomplete if the input flag END_OF_INPUT is not set as there might be more data to fill.
    #[inline]
    fn parse_many<I: Input, T, E, F, U>(self, I, F) -> ParseResult<I, T, E>
      where F: FnMut(I) -> ParseResult<I, U, E>,
            T: FromIterator<U>;

    /// Applies the parser `F` multiple times until it fails or the maximum value of the range has
    /// been reached, throwing away any produced value.
    ///
    /// Propagates errors if the minimum number of iterations has not been met
    ///
    /// # Panics
    ///
    /// Will panic if the end of the range is smaller than the start of the range.
    ///
    /// # Notes
    ///
    /// * Must never yield more items than the upper bound of the range.
    /// * Use `combinators::bounded::many` instead of calling this trait method directly.
    /// * If the last parser succeeds on the last input item then this parser is still considered
    ///   incomplete if the input flag END_OF_INPUT is not set as there might be more data to fill.
    #[inline]
    fn skip_many<I: Input, T, E, F>(self, I, F) -> ParseResult<I, (), E>
      where F: FnMut(I) -> ParseResult<I, T, E>;

    // TODO: Fix documentation regarding incomplete
    /// Applies the parser `P` multiple times until the parser `F` succeeds and returns a value
    /// populated by the values yielded by `P`. Consumes the matched part of `F`. If `F` does not
    /// succeed within the given range `R` this combinator will propagate any failure from `P`.
    ///
    /// # Panics
    ///
    /// Will panic if the end of the range is smaller than the start of the range.
    ///
    /// # Notes
    ///
    /// * Will allocate depending on the `FromIterator` implementation.
    /// * Use `combinators::bounded::many_till` instead of calling this trait method directly.
    /// * Must never yield more items than the upper bound of the range.
    /// * If the last parser succeeds on the last input item then this combinator is still considered
    ///   incomplete unless the parser `F` matches or the lower bound has not been met.
    #[inline]
    fn many_till<I: Input, T, E, R, F, U, N, V>(self, I, R, F) -> ParseResult<I, T, E>
      where T: FromIterator<U>,
            E: From<N>,
            R: FnMut(I) -> ParseResult<I, U, E>,
            F: FnMut(I) -> ParseResult<I, V, N>;
}

impl BoundedRange for Range<usize> {
    #[inline]
    fn parse_many<I: Input, T, E, F, U>(self, i: I, f: F) -> ParseResult<I, T, E>
      where F: FnMut(I) -> ParseResult<I, U, E>,
            T: FromIterator<U> {
        // Range does not perform this assertion
        assert!(self.start <= self.end);

        run_iter!{
            input:  i,
            parser: f,
            // Range is closed on left side, open on right, ie. [self.start, self.end)
            state:  (usize, usize): (self.start, max(self.end, 1) - 1),

            size_hint(self) {
                (self.data.0, Some(self.data.1))
            }

            next(self) {
                pre {
                    if self.data.1 == 0 {
                        return None;
                    }
                }
                on {
                    // TODO: Saturating sub?
                    self.data.0  = if self.data.0 == 0 { 0 } else { self.data.0 - 1 };
                    self.data.1 -= 1;
                }
            }

            => result : T {
                // Got all occurrences of the parser
                // First state or reached max => do not restore to mark since it is from last
                // iteration
                (s, (0, 0), _, _)            => s.ret(result),
                // Ok, last parser failed and we have reached minimum, we have iterated all.
                // Return remainder of buffer and the collected result
                (s, (0, _), m, Some(_))      => s.restore(m).ret(result),
                // Did not reach minimum, propagate
                (s, (_, _), _, Some(e))      => s.err(e),
                (_, _, _, None) => unreachable!(),
            }
        }
    }

    #[inline]
    fn skip_many<I: Input, T, E, F>(self, mut i: I, mut f: F) -> ParseResult<I, (), E>
      where F: FnMut(I) -> ParseResult<I, T, E> {
        // Range does not perform this assertion
        assert!(self.start <= self.end);

        // Closed on left side, open on right
        let (mut min, mut max) = (self.start, max(self.end, 1) - 1);

        loop {
            if max == 0 {
                break;
            }

            let m = i.mark();

            match f(i).into_inner() {
                (b, Ok(_))    => {
                    min  = if min == 0 { 0 } else { min - 1 };
                    max -= 1;

                    i = b
                },
                (b, Err(e))   => if min == 0 {
                    i = b.restore(m);

                    break;
                } else {
                    // Not enough iterations, propagate
                    return b.err(e);
                },
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<I: Input, T, E, R, F, U, N, V>(self, i: I, p: R, end: F) -> ParseResult<I, T, E>
      where T: FromIterator<U>,
            E: From<N>,
            R: FnMut(I) -> ParseResult<I, U, E>,
            F: FnMut(I) -> ParseResult<I, V, N> {
        // Range does not perform this assertion
        assert!(self.start <= self.end);

        run_iter_till!{
            input:  i,
            parser: p,
            end:    end,
            // Range is closed on left side, open on right, ie. [self.start, self.end)
            state:  (usize, usize): (self.start, max(self.end, 1) - 1),

            size_hint(self) {
                (self.data.0, Some(self.data.1))
            }

            next(self) {
                pre {
                    if self.data.0 == 0 {
                        // We have reached minimum, we can attempt to end now

                        // TODO: Remove the branches here (ie. take + unwrap)
                        let i = self.buf.take().expect("Iter.buf was None");
                        let m = i.mark();

                        match (self.data.1, (self.end)(i).into_inner()) {
                            // We can always end
                            (_, (b, Ok(_))) => {
                                self.buf   = Some(b);
                                self.state = EndStateTill::EndSuccess;

                                return None
                            },
                            // We have reached end, end must match or it is an error
                            (0, (b, Err(e)))      => {
                                self.buf   = Some(b);
                                self.state = EndStateTill::Error(From::from(e));

                                return None;
                            },
                            // Failed to end, restore and continue since we can parse more
                            (_, (b, Err(_)))      => self.buf = Some(b.restore(m)),
                        }
                    }
                }
                on {
                    self.data.0  = if self.data.0 == 0 { 0 } else { self.data.0 - 1 };
                    self.data.1 -= 1;
                }
            }

            => result : T {
                // Got all occurrences of the parser
                (s, (0, _), EndStateTill::EndSuccess)    => s.ret(result),
                // Did not reach minimum or a failure, propagate
                (s, (_, _), EndStateTill::Error(e))   => s.err(e),
                (_, (_, _), EndStateTill::Incomplete) => unreachable!(),
                // We cannot reach this since we only run the end test once we have reached the
                // minimum number of matches
                (_, (_, _), EndStateTill::EndSuccess)    => unreachable!()
            }
        }
    }
}

impl BoundedRange for RangeFrom<usize> {
    #[inline]
    fn parse_many<I: Input, T, E, F, U>(self, i: I, f: F) -> ParseResult<I, T, E>
      where F: FnMut(I) -> ParseResult<I, U, E>,
            T: FromIterator<U> {
        run_iter!{
            input:  i,
            parser: f,
            // Inclusive
            state:  usize: self.start,

            size_hint(self) {
                (self.data, None)
            }

            next(self) {
                pre {}
                on  {
                    self.data = if self.data == 0 { 0 } else { self.data - 1 };
                }
            }

            => result : T {
                // We got at least n items
                (s, 0, m, Some(_))      => s.restore(m).ret(result),
                // Items still remaining, propagate
                (s, _, _, Some(e))      => s.err(e),
                (_, _, _, None) => unreachable!(),
            }
        }
    }

    #[inline]
    fn skip_many<I: Input, T, E, F>(self, mut i: I, mut f: F) -> ParseResult<I, (), E>
      where F: FnMut(I) -> ParseResult<I, T, E> {
        // Closed on left side, open on right
        let mut min = self.start;

        loop {
            let m = i.mark();

            match f(i).into_inner() {
                (b, Ok(_))    => {
                    min  = if min == 0 { 0 } else { min - 1 };

                    i = b
                },
                (b, Err(e))   => if min == 0 {
                    i = b.restore(m);

                    break;
                } else {
                    // Not enough iterations, propagate
                    return b.err(e);
                },
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<I: Input, T, E, R, F, U, N, V>(self, i: I, p: R, end: F) -> ParseResult<I, T, E>
      where T: FromIterator<U>,
            E: From<N>,
            R: FnMut(I) -> ParseResult<I, U, E>,
            F: FnMut(I) -> ParseResult<I, V, N> {
        run_iter_till!{
            input:  i,
            parser: p,
            end:    end,
            // Range is closed on left side, unbounded on right
            state:  usize: self.start,

            size_hint(self) {
                (self.data, None)
            }

            next(self) {
                pre {
                    if self.data == 0 {
                        // We have reached minimum, we can attempt to end now
                        iter_till_end_test!(self);
                    }
                }
                on {
                    self.data = if self.data == 0 { 0 } else { self.data - 1 };
                }
            }

            => result : T {
                // Got all occurrences of the parser
                (s, 0, EndStateTill::EndSuccess)    => s.ret(result),
                // Did not reach minimum or a failure, propagate
                (s, _, EndStateTill::Error(e))   => s.err(e),
                (_, _, EndStateTill::Incomplete) => unreachable!(),
                // We cannot reach this since we only run the end test once we have reached the
                // minimum number of matches
                (_, _, EndStateTill::EndSuccess)    => unreachable!()
            }
        }
    }
}

impl BoundedRange for RangeFull {
    #[inline]
    fn parse_many<I: Input, T, E, F, U>(self, i: I, f: F) -> ParseResult<I, T, E>
      where F: FnMut(I) -> ParseResult<I, U, E>,
            T: FromIterator<U> {
        run_iter!{
            input:  i,
            parser: f,
            state:  (): (),

            size_hint(self) {
                (0, None)
            }

            next(self) {
                pre {}
                on  {}
            }

            => result : T {
                (s, (), m, Some(_)) => s.restore(m).ret(result),
                (_, _, _, None)     => unreachable!(),
            }
        }
    }

    #[inline]
    fn skip_many<I: Input, T, E, F>(self, mut i: I, mut f: F) -> ParseResult<I, (), E>
      where F: FnMut(I) -> ParseResult<I, T, E> {
        loop {
            let m = i.mark();

            match f(i).into_inner() {
                (b, Ok(_))  => i = b,
                (b, Err(_)) => {
                    i = b.restore(m);

                    break;
                },
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<I: Input, T, E, R, F, U, N, V>(self, i: I, p: R, end: F) -> ParseResult<I, T, E>
      where T: FromIterator<U>,
            E: From<N>,
            R: FnMut(I) -> ParseResult<I, U, E>,
            F: FnMut(I) -> ParseResult<I, V, N> {
        run_iter_till!{
            input:  i,
            parser: p,
            end:    end,
            state:  (): (),

            size_hint(self) {
                (0, None)
            }

            next(self) {
                pre {
                    // Can end at any time
                    iter_till_end_test!(self);
                }
                on  {}
            }

            => result : T {
                (s, (), EndStateTill::EndSuccess)    => s.ret(result),
                (s, (), EndStateTill::Error(e))      => s.err(e),
                // Nested parser incomplete, propagate if not at end
                (_, (), EndStateTill::Incomplete) => unreachable!()
            }
        }
    }
}

impl BoundedRange for RangeTo<usize> {
    #[inline]
    fn parse_many<I: Input, T, E, F, U>(self, i: I, f: F) -> ParseResult<I, T, E>
      where F: FnMut(I) -> ParseResult<I, U, E>,
            T: FromIterator<U> {
        run_iter!{
            input:  i,
            parser: f,
            // Exclusive range [0, end)
            state:  usize:  max(self.end, 1) - 1,

            size_hint(self) {
                (0, Some(self.data))
            }

            next(self) {
                pre {
                    if self.data == 0 {
                        return None;
                    }
                }
                on {
                    self.data  -= 1;
                }
            }

            => result : T {
                // First state or reached max => do not restore to mark since it is from last
                // iteration
                (s, 0, _, _)                       => s.ret(result),
                // Inside of range, never outside
                (s, _, m, Some(_))      => s.restore(m).ret(result),
                (_, _, _, None) => unreachable!(),
            }
        }
    }

    #[inline]
    fn skip_many<I: Input, T, E, F>(self, mut i: I, mut f: F) -> ParseResult<I, (), E>
      where F: FnMut(I) -> ParseResult<I, T, E> {
        // [0, n)
        let mut max = max(self.end, 1) - 1;

        loop {
            if max == 0 {
                break;
            }

            let m = i.mark();

            match f(i).into_inner() {
                (b, Ok(_))    => {
                    max -= 1;

                    i = b
                },
                // Always ok to end iteration
                (b, Err(_))   => {
                    i = b.restore(m);

                    break;
                },
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<I: Input, T, E, R, F, U, N, V>(self, i: I, p: R, end: F) -> ParseResult<I, T, E>
      where T: FromIterator<U>,
            E: From<N>,
            R: FnMut(I) -> ParseResult<I, U, E>,
            F: FnMut(I) -> ParseResult<I, V, N> {
        run_iter_till!{
            input:  i,
            parser: p,
            end:    end,
            // [0, self.end)
            state:  usize: max(self.end, 1) - 1,

            size_hint(self) {
                (0, Some(self.data))
            }

            next(self) {
                pre {
                    // TODO: Remove the branches here (ie. take + unwrap)
                    let i = self.buf.take().expect("Iter.buf was None");
                    let m = i.mark();

                    match (self.data, (self.end)(i).into_inner()) {
                        // We can always end
                        (_, (b, Ok(_))) => {
                            self.buf   = Some(b);
                            self.state = EndStateTill::EndSuccess;

                            return None
                        },
                        // We have reached end, end must match or it is an error
                        (0, (b, Err(e)))      => {
                            self.buf   = Some(b);
                            self.state = EndStateTill::Error(From::from(e));

                            return None;
                        },
                        // Failed to end, restore and continue since we can parse more
                        (_, (b, Err(_)))      => self.buf = Some(b.restore(m)),
                    }
                }
                on {
                    self.data -= 1;
                }
            }

            => result : T {
                // Got all occurrences of the parser since we have no minimum bound
                (s, _, EndStateTill::EndSuccess)    => s.ret(result),
                // Did not reach minimum or a failure, propagate
                (s, _, EndStateTill::Error(e))   => s.err(e),
                (_, _, EndStateTill::Incomplete) => unreachable!(),
            }
        }
    }
}

impl BoundedRange for usize {
    // TODO: Any way to avoid marking for backtracking here?
    #[inline]
    fn parse_many<I: Input, T, E, F, U>(self, i: I, f: F) -> ParseResult<I, T, E>
      where F: FnMut(I) -> ParseResult<I, U, E>,
            T: FromIterator<U> {
        run_iter!{
            input:  i,
            parser: f,
            // Excatly self
            state:  usize: self,

            size_hint(self) {
                (self.data, Some(self.data))
            }

            next(self) {
                pre {
                    if self.data == 0 {
                        return None;
                    }
                }
                on {
                    self.data  -= 1;
                }
            }

            => result : T {
                // Got exact
                (s, 0, _, _)                       => s.ret(result),
                // We have got too few items, propagate error
                (s, _, _, Some(e))      => s.err(e),
                (_, _, _, None) => unreachable!(),
            }
        }
    }

    #[inline]
    fn skip_many<I: Input, T, E, F>(self, mut i: I, mut f: F) -> ParseResult<I, (), E>
      where F: FnMut(I) -> ParseResult<I, T, E> {
        let mut n = self;

        loop {
            if n == 0 {
                break;
            }

            match f(i).into_inner() {
                (b, Ok(_))    => {
                    n -= 1;

                    i = b
                },
                (b, Err(e))   => if n == 0 {
                    unreachable!();
                } else {
                    // Not enough iterations, propagate
                    return b.err(e);
                },
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<I: Input, T, E, R, F, U, N, V>(self, i: I, p: R, end: F) -> ParseResult<I, T, E>
      where T: FromIterator<U>,
            E: From<N>,
            R: FnMut(I) -> ParseResult<I, U, E>,
            F: FnMut(I) -> ParseResult<I, V, N> {
        run_iter_till!{
            input:  i,
            parser: p,
            end:    end,
            state:  usize: self,

            size_hint(self) {
                (self.data, Some(self.data))
            }

            next(self) {
                pre {
                    if self.data == 0 {
                        // Attempt to make a successful end
                        iter_till_end_test!(self);

                        return None;
                    }
                }
                on {
                    self.data -= 1;
                }
            }

            => result : T {
                // Got all occurrences of the parser
                (s, 0, EndStateTill::EndSuccess)    => s.ret(result),
                // Did not reach minimum or a failure, propagate
                (s, _, EndStateTill::Error(e))      => s.err(e),
                (_, _, EndStateTill::Incomplete) => unreachable!(),
                // We cannot reach this since we only run the end test once we have reached the
                // minimum number of matches
                (_, _, EndStateTill::EndSuccess)    => unreachable!()
            }
        }
    }
}

/// Applies the parser `F` multiple times until it fails or the maximum value of the range has
/// been reached, collecting the successful values into a `T: FromIterator`.
///
/// Propagates errors if the minimum number of iterations has not been met
///
/// # Panics
///
/// Will panic if the end of the range is smaller than the start of the range.
///
/// # Notes
///
/// * Will allocate depending on the `FromIterator` implementation.
/// * Will never yield more items than the upper bound of the range.
#[inline]
pub fn many<I: Input, T, E, F, U, R>(i: I, r: R, f: F) -> ParseResult<I, T, E>
  where R: BoundedRange,
        F: FnMut(I) -> ParseResult<I, U, E>,
        T: FromIterator<U> {
    BoundedRange::parse_many(r, i, f)
}

/// Applies the parser `F` multiple times until it fails or the maximum value of the range has
/// been reached, throwing away any produced value.
///
/// Propagates errors if the minimum number of iterations has not been met
///
/// # Panics
///
/// Will panic if the end of the range is smaller than the start of the range.
///
/// # Notes
///
/// * Will never yield more items than the upper bound of the range.
#[inline]
pub fn skip_many<I: Input, T, E, F, R>(i: I, r: R, f: F) -> ParseResult<I, (), E>
  where R: BoundedRange,
        F: FnMut(I) -> ParseResult<I, T, E> {
    BoundedRange::skip_many(r, i, f)
}

// TODO: Update documentation regarding incomplete behaviour
/// Applies the parser `P` multiple times until the parser `F` succeeds and returns a value
/// populated by the values yielded by `P`. Consumes the matched part of `F`. If `F` does not
/// succeed within the given range `R` this combinator will propagate any failure from `P`.
///
/// # Panics
///
/// Will panic if the end of the range is smaller than the start of the range.
///
/// # Notes
///
/// * Will allocate depending on the `FromIterator` implementation.
/// * Will never yield more items than the upper bound of the range.
#[inline]
pub fn many_till<I: Input, T, E, R, F, U, N, P, V>(i: I, r: R, p: P, end: F) -> ParseResult<I, T, E>
  where R: BoundedRange,
        T: FromIterator<U>,
        E: From<N>,
        P: FnMut(I) -> ParseResult<I, U, E>,
        F: FnMut(I) -> ParseResult<I, V, N> {
    BoundedRange::many_till(r, i, p, end)
}

/// Applies the parser `p` multiple times, separated by the parser `sep` and returns a value
/// populated with the values yielded by `p`. If the number of items yielded by `p` does not fall
/// into the range `r` and the separator or parser registers error or incomplete failure is
/// propagated.
///
/// # Panics
///
/// Will panic if the end of the range is smaller than the start of the range.
///
/// # Notes
///
/// * Will allocate depending on the `FromIterator` implementation.
/// * Will never yield more items than the upper bound of the range.
#[inline]
pub fn sep_by<I: Input, T, E, R, F, U, N, P, V>(i: I, r: R, mut p: P, mut sep: F) -> ParseResult<I, T, E>
  where T: FromIterator<U>,
        E: From<N>,
        R: BoundedRange,
        P: FnMut(I) -> ParseResult<I, U, E>,
        F: FnMut(I) -> ParseResult<I, V, N> {
    // If we have parsed at least one item
    let mut item = false;
    // Add sep in front of p if we have read at least one item
    let parser   = |i| (if item {
            sep(i).map(|_| ())
        } else {
            i.ret(())
        })
        .then(&mut p)
        .inspect(|_| item = true);

    BoundedRange::parse_many(r, i, parser)
}

#[cfg(test)]
mod test {
    use types::ParseResult;
    use parsers::{Error, any, token, string};
    use primitives::IntoInner;

    use super::{
        many,
        many_till,
        skip_many,
    };

    #[test]
    fn many_range_full() {
        let r: ParseResult<_, Vec<_>, _> = many(&b"b"[..],   .., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ab"[..],  .., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(vec![b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aab"[..], .., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(vec![b'a', b'a'])));

        let r: ParseResult<_, Vec<_>, _> = many(&b""[..],   .., any); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..],  .., any); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aa"[..], .., any); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r: ParseResult<_, Vec<_>, _> = many(&b"abac"[..], .., |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"abac"[..], .., |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aba"[..],  .., |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![&b"ab"[..]])));
    }

    #[test]
    fn many_range_to() {
        let r: ParseResult<_, Vec<_>, _> = many(&b""[..], ..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..], ..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![])));

        let r: ParseResult<_, Vec<_>, _> = many(&b""[..], ..1, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..], ..1, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![])));

        let r: ParseResult<_, Vec<_>, _> = many(&b""[..], ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..], ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aa"[..], ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a', b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaa"[..], ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r: ParseResult<_, Vec<_>, _> = many(&b"abac"[..], ..3, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"abac"[..], ..3, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aba"[..], ..3, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![&b"ab"[..]])));
    }

    #[test]
    fn many_range_from() {
        let r: ParseResult<_, Vec<_>, _> = many(&b""[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aa"[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a', b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaa"[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a', b'a', b'a'])));

        let r: ParseResult<_, Vec<_>, _> = many(&b"b"[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ab"[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aab"[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(vec![b'a', b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaab"[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(vec![b'a', b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r: ParseResult<_, Vec<_>, _> = many(&b"ababac"[..], 2.., |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"ac"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ababac"[..], 2.., |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"ac"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ababa"[..],  2.., |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
    }

    #[test]
    fn many_range() {
        let r: ParseResult<_, Vec<_>, _> = many(&b""[..], 0..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..], 0..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b""[..], 0..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..], 0..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![])));

        let r: ParseResult<_, Vec<_>, _> = many(&b""[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aa"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a', b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaa"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a', b'a', b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaaa"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![b'a', b'a', b'a'])));

        let r: ParseResult<_, Vec<_>, _> = many(&b"b"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ab"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aab"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(vec![b'a', b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaab"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(vec![b'a', b'a', b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaaab"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"ab"[..], Ok(vec![b'a', b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r: ParseResult<_, Vec<_>, _> = many(&b"abac"[..], 1..3, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ababac"[..], 1..3, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"ac"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
    }

    #[test]
    fn many_exact() {
        let r: ParseResult<_, Vec<_>, _> = many(&b""[..],    0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..],   0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aa"[..],  0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"aa"[..], Ok(vec![])));

        let r: ParseResult<_, Vec<_>, _> = many(&b""[..],    2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"a"[..],   2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aa"[..],  2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![b'a', b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaa"[..], 2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![b'a', b'a'])));

        let r: ParseResult<_, Vec<_>, _> = many(&b"b"[..],    2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ab"[..],   2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aab"[..],  2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(vec![b'a', b'a'])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaab"[..], 2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"ab"[..], Ok(vec![b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r: ParseResult<_, Vec<_>, _> = many(&b"abac"[..],   2, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"c"[..], Err(Error::expected(b'b'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ababa"[..],  2, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"abac"[..],   2, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"c"[..], Err(Error::expected(b'b'))));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ababac"[..], 2, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"ac"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many(&b"ababa"[..],  2, |i| string(i, b"ab")); assert_eq!(r.into_inner(), (&b"a"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
    }

    #[test]
    fn many_till_range_full() {
        let r: ParseResult<_, Vec<_>, _> = many_till(&b""[..],        .., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..],      .., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..],    .., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ababac"[..],  .., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ababab"[..],  .., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abababa"[..], .., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'b'))));
    }

    #[test]
    fn many_till_range_from() {
        let r: ParseResult<_, Vec<_>, _> = many_till(&b""[..], 0.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"a"[..], 0.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'b'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ab"[..], 0.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..], 0.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..], 1.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"c"[..], Err(Error::expected(b'b'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..], 0.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..], 1.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..], 2.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"c"[..], Err(Error::expected(b'b'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ababac"[..], 2.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ababab"[..], 2.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abababa"[..], 2.., |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'b'))));
    }

    #[test]
    fn many_till_range_to() {
        let r: ParseResult<_, Vec<_>, _> = many_till(&b""[..],         ..0, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"b"[..],        ..0, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"a"[..],        ..0, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..],       ..0, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b""[..],         ..1, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..],       ..1, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..],     ..2, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b""[..],         ..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..],       ..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..],     ..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ababac"[..],   ..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abababac"[..], ..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"bac"[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ababab"[..],   ..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ababa"[..],    ..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abababa"[..],  ..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"ba"[..], Err(Error::expected(b'c'))));
    }

    #[test]
    fn many_till_range() {
        let r: ParseResult<_, Vec<_>, _> = many_till(&b""[..],   0..0, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b""[..],   0..0, |i| string(i, b"ab"), |i| string(i, b"cd")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"a"[..],  0..0, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..], 0..0, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));

        let r: ParseResult<_, Vec<_>, _> = many_till(&b""[..],   0..1, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..], 0..1, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ab"[..], 0..1, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..], 0..1, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"bac"[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..],   0..2, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..], 0..2, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b""[..],         0..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"a"[..],         0..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'b'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..],       0..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abc"[..],      0..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"c"[..], Err(Error::expected(b'a'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..],     0..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ababac"[..],   0..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abababac"[..], 0..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"bac"[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ababa"[..],    0..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'c'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abababa"[..],  0..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"ba"[..], Err(Error::expected(b'c'))));

        let r: ParseResult<_, Vec<_>, _> = many_till(&b"ac"[..], 1..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"c"[..], Err(Error::expected(b'b'))));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..], 1..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"abac"[..], 2..3, |i| string(i, b"ab"), |i| string(i, b"ac")); assert_eq!(r.into_inner(), (&b"c"[..], Err(Error::expected(b'b'))));
    }

    #[test]
    fn skip_range_full() {
        let r = skip_many(&b""[..],   .., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"a"[..],  .., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"aa"[..], .., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));

        let r = skip_many(&b"b"[..],   .., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
        let r = skip_many(&b"ab"[..],  .., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
        let r = skip_many(&b"aab"[..], .., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
    }

    #[test]
    fn skip_range_to() {
        let r = skip_many(&b""[..],  ..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"a"[..], ..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(())));

        let r = skip_many(&b""[..],    ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"a"[..],   ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"aa"[..],  ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"aaa"[..], ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(())));

        let r = skip_many(&b"b"[..],    ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
        let r = skip_many(&b"ab"[..],   ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
        let r = skip_many(&b"aab"[..],  ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
        let r = skip_many(&b"aaab"[..], ..3, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"ab"[..], Ok(())));
    }

    #[test]
    fn skip_range_from() {
        let r = skip_many(&b""[..],    2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(&b"a"[..],   2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(&b"aa"[..],  2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"aaa"[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));

        let r = skip_many(&b"b"[..],    2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r = skip_many(&b"ab"[..],   2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r = skip_many(&b"aab"[..],  2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
        let r = skip_many(&b"aaab"[..], 2.., |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
    }

    #[test]
    fn skip_range() {
        let r = skip_many(&b""[..],  0..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"a"[..], 0..0, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(())));

        let r = skip_many(&b""[..],     2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(&b"a"[..],    2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(&b"aa"[..],   2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"aaa"[..],  2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..], Ok(())));
        let r = skip_many(&b"aaaa"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..], Ok(())));

        let r = skip_many(&b"b"[..],     2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r = skip_many(&b"ab"[..],    2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Err(Error::expected(b'a'))));
        let r = skip_many(&b"aab"[..],   2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
        let r = skip_many(&b"aaab"[..],  2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..], Ok(())));
        let r = skip_many(&b"aaaab"[..], 2..4, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"ab"[..], Ok(())));
    }

    #[test]
    fn skip_exact() {
        let r = skip_many(&b""[..],     2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..],   Err(Error::expected(b'a'))));
        let r = skip_many(&b"a"[..],    2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..],   Err(Error::expected(b'a'))));
        let r = skip_many(&b"aa"[..],   2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b""[..],   Ok(())));
        let r = skip_many(&b"aaa"[..],  2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"a"[..],  Ok(())));
        let r = skip_many(&b"aaab"[..], 2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"ab"[..], Ok(())));
        let r = skip_many(&b"aab"[..],  2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..],  Ok(())));
        let r = skip_many(&b"ab"[..],   2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..],  Err(Error::expected(b'a'))));
        let r = skip_many(&b"b"[..],    2, |i| token(i, b'a')); assert_eq!(r.into_inner(), (&b"b"[..],  Err(Error::expected(b'a'))));
    }

    #[test]
    #[should_panic]
    fn panic_many_range_lt() {
        let r: ParseResult<_, Vec<_>, _> = many(&b"aaaab"[..], 2..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), (&b"ab"[..], Ok(vec![b'a', b'a', b'a'])));
    }

    #[test]
    #[should_panic]
    fn panic_skip_many_range_lt() {
        assert_eq!(skip_many(&b"aaaab"[..], 2..1, |i| token(i, b'a')).into_inner(), (&b"ab"[..], Ok(())));
    }

    #[test]
    #[should_panic]
    fn panic_many_till_range_lt() {
        let r: ParseResult<_, Vec<_>, _> = many_till(&b"aaaab"[..], 2..1, |i| token(i, b'a'), |i| token(i, b'b'));
        assert_eq!(r.into_inner(), (&b"ab"[..], Ok(vec![b'a', b'a', b'a'])));
    }
}
