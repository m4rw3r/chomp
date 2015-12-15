//! Bounded versions of combinators.
//!
//! This module provides bounded versions of `many`, `many_till` and `skip_many`.
//!
//! The core range types are used to describe a half-open range of successive applications of a
//! parser. `usize` is used to specify an exact number of iterations:
//!
//! ```
//! use chomp::combinators::bounded::many;
//! use chomp::{Input, ParseResult, any};
//!
//! let i = Input::new(b"abcd");
//! // Read any character 2 or 3 times
//! let r: ParseResult<_, Vec<_>, _> = many(i, 2..4, any);
//!
//! assert_eq!(r.unwrap(), vec![b'a', b'b', b'c']);
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

use {Input, ParseResult};
use primitives::{InputClone, InputBuffer, IntoInner, State};

/// Trait for applying a parser multiple times based on a range.
pub trait BoundedRange {
    /// Applies the parser `F` multiple times until it fails or the maximum value of the range has
    /// been reached, collecting the successful values into a `T: FromIterator`.
    ///
    /// Propagates errors if the minimum number of iterations has not been met
    ///
    /// # Notes
    ///
    /// * Will allocate depending on the `FromIterator` implementation.
    /// * Must never yield more items than the upper bound of the range.
    /// * Use `combinators::bounded::many` instead of calling this trait method directly.
    /// * If the last parser succeeds on the last input item then this parser is still considered
    ///   incomplete if the input flag END_OF_INPUT is not set as there might be more data to fill.
    #[inline]
    fn parse_many<'a, I, T, E, F, U>(self, Input<'a, I>, F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            T: FromIterator<U>;

    /// Applies the parser `F` multiple times until it fails or the maximum value of the range has
    /// been reached, throwing away any produced value.
    ///
    /// Propagates errors if the minimum number of iterations has not been met
    ///
    /// # Notes
    ///
    /// * Must never yield more items than the upper bound of the range.
    /// * Use `combinators::bounded::many` instead of calling this trait method directly.
    /// * If the last parser succeeds on the last input item then this parser is still considered
    ///   incomplete if the input flag END_OF_INPUT is not set as there might be more data to fill.
    #[inline]
    fn skip_many<'a, I, T, E, F>(self, Input<'a, I>, F) -> ParseResult<'a, I, (), E>
      where T: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E>;

    /// Applies the parser `P` multiple times until the parser `F` succeeds and returns a value
    /// populated by the values yielded by `P`. Consumes the matched part of `F`. If `F` does not
    /// succeed within the given range `R` this combinator will propagate any failure from `P`.
    ///
    /// # Notes
    ///
    /// * Will allocate depending on the `FromIterator` implementation.
    /// * Use `combinators::bounded::many_till` instead of calling this trait method directly.
    /// * Must never yield more items than the upper bound of the range.
    /// * If the last parser succeeds on the last input item then this combinator is still considered
    ///   incomplete unless the parser `F` matches or the lower bound has not been met.
    #[inline]
    fn many_till<'a, I, T, E, R, F, U, N, V>(self, i: Input<'a, I>, p: R, end: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            V: 'a,
            N: 'a,
            T: FromIterator<U>,
            R: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, V, N>;
}

impl BoundedRange for Range<usize> {
    #[inline]
    fn parse_many<'a, I, T, E, F, U>(self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
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
                    self.data.0  = if self.data.0 == 0 { 0 } else { self.data.0 - 1 };
                    self.data.1 -= 1;
                }
            }

            => result : T {
                // Got all occurrences of the parser
                (s, (0, 0), _) => s.ret(result),
                // Ok, last parser failed and we have reached minimum, we have iterated all.
                // Return remainder of buffer and the collected result
                (s, (0, _), EndState::Error(_, _))   => s.ret(result),
                // Nested parser incomplete but reached at least minimum, propagate if not at end
                (s, (0, _), EndState::Incomplete(n)) => if s.is_last_slice() {
                    s.ret(result)
                } else {
                    s.incomplete(n)
                },
                // Did not reach minimum, propagate
                (s, (_, _), EndState::Error(b, e))   => s.replace(b).err(e),
                (s, (_, _), EndState::Incomplete(n)) => s.incomplete(n)
            }
        }
    }

    #[inline]
    fn skip_many<'a, I, T, E, F>(self, mut i: Input<'a, I>, mut f: F) -> ParseResult<'a, I, (), E>
      where T: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
        // Range does not perform this assertion
        assert!(self.start <= self.end);

        // Closed on left side, open on right
        let (mut min, mut max) = (self.start, max(self.end, 1) - 1);

        loop {
            if max == 0 {
                break;
            }

            match f(i.clone()).into_inner() {
                State::Data(b, _)    => {
                    min  = if min == 0 { 0 } else { min - 1 };
                    max -= 1;

                    i = b
                },
                State::Error(b, e)   => if min == 0 {
                    break;
                } else {
                    // Not enough iterations
                    return i.replace(b).err(e);
                },
                State::Incomplete(n) => if min == 0 && i.is_last_slice() {
                    break;
                } else {
                    // We have not done the minimum amount of iterations
                    return i.incomplete(n);
                }
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<'a, I, T, E, R, F, U, N, V>(self, i: Input<'a, I>, p: R, end: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            V: 'a,
            N: 'a,
            T: FromIterator<U>,
            R: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, V, N> {
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
                        iter_till_end_test!(self);
                    }

                    // Maximum reached, stop iteration and check error state
                    if self.data.1 == 0 {
                        // Attempt to make a successful end
                        iter_till_end_test!(self);

                        return None;
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
                (s, (_, _), EndStateTill::Error(b, e))   => s.replace(b).err(e),
                (s, (_, _), EndStateTill::Incomplete(n)) => s.incomplete(n),
                // We cannot reach this since we only run the end test once we have reached the
                // minimum number of matches
                (_, (_, _), EndStateTill::EndSuccess)    => unreachable!()
            }
        }
    }
}

impl BoundedRange for RangeFrom<usize> {
    #[inline]
    fn parse_many<'a, I, T, E, F, U>(self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
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
                (s, 0, EndState::Error(_, _))   => s.ret(result),
                // Nested parser incomplete, propagate if not at end
                (s, 0, EndState::Incomplete(n)) => if s.is_last_slice() {
                    s.ret(result)
                } else {
                    s.incomplete(n)
                },
                // Items still remaining, propagate
                (s, _, EndState::Error(b, e))   => s.replace(b).err(e),
                (s, _, EndState::Incomplete(n)) => s.incomplete(n)
            }
        }
    }

    #[inline]
    fn skip_many<'a, I, T, E, F>(self, mut i: Input<'a, I>, mut f: F) -> ParseResult<'a, I, (), E>
      where T: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
        // Closed on left side, open on right
        let mut min = self.start;

        loop {
            match f(i.clone()).into_inner() {
                State::Data(b, _)    => {
                    min  = if min == 0 { 0 } else { min - 1 };

                    i = b
                },
                State::Error(b, e)   => if min == 0 {
                    break;
                } else {
                    // Not enough iterations
                    return i.replace(b).err(e);
                },
                State::Incomplete(n) => if min == 0 && i.is_last_slice() {
                    break;
                } else {
                    // We have not done the minimum amount of iterations
                    return i.incomplete(n);
                }
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<'a, I, T, E, R, F, U, N, V>(self, i: Input<'a, I>, p: R, end: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            V: 'a,
            N: 'a,
            T: FromIterator<U>,
            R: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, V, N> {
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
                (s, _, EndStateTill::Error(b, e))   => s.replace(b).err(e),
                (s, _, EndStateTill::Incomplete(n)) => s.incomplete(n),
                // We cannot reach this since we only run the end test once we have reached the
                // minimum number of matches
                (_, _, EndStateTill::EndSuccess)    => unreachable!()
            }
        }
    }
}

impl BoundedRange for RangeFull {
    #[inline]
    fn parse_many<'a, I, T, E, F, U>(self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
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
                (s, (), EndState::Error(_, _))   => s.ret(result),
                // Nested parser incomplete, propagate if not at end
                (s, (), EndState::Incomplete(n)) => if s.is_last_slice() {
                    s.ret(result)
                } else {
                    s.incomplete(n)
                }
            }
        }
    }

    #[inline]
    fn skip_many<'a, I, T, E, F>(self, mut i: Input<'a, I>, mut f: F) -> ParseResult<'a, I, (), E>
      where T: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
        loop {
            match f(i.clone()).into_inner() {
                State::Data(b, _)    => i = b,
                State::Error(_, _)   => break,
                State::Incomplete(n) => if i.is_last_slice() {
                    break;
                } else {
                    return i.incomplete(n);
                }
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<'a, I, T, E, R, F, U, N, V>(self, i: Input<'a, I>, p: R, end: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            V: 'a,
            N: 'a,
            T: FromIterator<U>,
            R: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, V, N> {
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
                (s, (), EndStateTill::Error(b, e))   => s.replace(b).err(e),
                // Nested parser incomplete, propagate if not at end
                (s, (), EndStateTill::Incomplete(n)) => s.incomplete(n)
            }
        }
    }
}

impl BoundedRange for RangeTo<usize> {
    #[inline]
    fn parse_many<'a, I, T, E, F, U>(self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
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
                // Either error or incomplete after the end
                (s, 0, _)                       => s.ret(result),
                // Inside of range, never outside
                (s, _, EndState::Error(_, _))   => s.ret(result),
                // Nested parser incomplete, propagate if not at end
                (s, _, EndState::Incomplete(n)) => if s.is_last_slice() {
                    s.ret(result)
                } else {
                    s.incomplete(n)
                }
            }
        }
    }

    #[inline]
    fn skip_many<'a, I, T, E, F>(self, mut i: Input<'a, I>, mut f: F) -> ParseResult<'a, I, (), E>
      where T: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
        // [0, n)
        let mut max = max(self.end, 1) - 1;

        loop {
            if max == 0 {
                break;
            }

            match f(i.clone()).into_inner() {
                State::Data(b, _)    => {
                    max -= 1;

                    i = b
                },
                // Always ok to end iteration
                State::Error(_, _)   => break,
                State::Incomplete(n) => if i.is_last_slice() {
                    break;
                } else {
                    return i.incomplete(n);
                }
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<'a, I, T, E, R, F, U, N, V>(self, i: Input<'a, I>, p: R, end: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            V: 'a,
            N: 'a,
            T: FromIterator<U>,
            R: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, V, N> {
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
                    // Can end at any time
                    iter_till_end_test!(self);

                    // Maximum reached, stop iteration and check error state
                    if self.data == 0 {
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
                (s, _, EndStateTill::Error(b, e))   => s.replace(b).err(e),
                (s, _, EndStateTill::Incomplete(n)) => s.incomplete(n),
                // We cannot reach this since we only run the end test once we have reached the
                // minimum number of matches
                (_, _, EndStateTill::EndSuccess)    => unreachable!()
            }
        }
    }
}

impl BoundedRange for usize {
    #[inline]
    fn parse_many<'a, I, T, E, F, U>(self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
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
                (s, 0, _)                       => s.ret(result),
                // We have got too few items, propagate error
                (s, _, EndState::Error(b, e))   => s.replace(b).err(e),
                // Nested parser incomplete, propagate
                (s, _, EndState::Incomplete(n)) => s.incomplete(n)
            }
        }
    }

    #[inline]
    fn skip_many<'a, I, T, E, F>(self, mut i: Input<'a, I>, mut f: F) -> ParseResult<'a, I, (), E>
      where T: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
        let mut n = self;

        loop {
            if n == 0 {
                break;
            }

            match f(i.clone()).into_inner() {
                State::Data(b, _)    => {
                    n -= 1;

                    i = b
                },
                State::Error(b, e)   => if n == 0 {
                    break;
                } else {
                    // Not enough iterations
                    return i.replace(b).err(e);
                },
                State::Incomplete(n) => if n == 0 {
                    break;
                } else {
                    return i.incomplete(n);
                }
            }
        }

        i.ret(())
    }

    #[inline]
    fn many_till<'a, I, T, E, R, F, U, N, V>(self, i: Input<'a, I>, p: R, end: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            V: 'a,
            N: 'a,
            T: FromIterator<U>,
            R: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, V, N> {
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
                (s, _, EndStateTill::Error(b, e))   => s.replace(b).err(e),
                (s, _, EndStateTill::Incomplete(n)) => s.incomplete(n),
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
/// # Notes
///
/// * Will allocate depending on the `FromIterator` implementation.
/// * Will never yield more items than the upper bound of the range.
/// * If the last parser succeeds on the last input item then this parser is still considered
///   incomplete if the input flag END_OF_INPUT is not set as there might be more data to fill.
#[inline]
pub fn many<'a, I, T, E, F, U, R>(i: Input<'a, I>, r: R, f: F) -> ParseResult<'a, I, T, E>
  where I: Copy,
        R: BoundedRange,
        U: 'a,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
        T: FromIterator<U> {
    BoundedRange::parse_many(r, i, f)
}

/// Applies the parser `F` multiple times until it fails or the maximum value of the range has
/// been reached, throwing away any produced value.
///
/// Propagates errors if the minimum number of iterations has not been met
///
/// # Notes
///
/// * Will never yield more items than the upper bound of the range.
/// * If the last parser succeeds on the last input item then this parser is still considered
///   incomplete if the input flag END_OF_INPUT is not set as there might be more data to fill.
#[inline]
pub fn skip_many<'a, I, T, E, F, R>(i: Input<'a, I>, r: R, f: F) -> ParseResult<'a, I, (), E>
  where T: 'a,
        R: BoundedRange,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
    BoundedRange::skip_many(r, i, f)
}

/// Applies the parser `P` multiple times until the parser `F` succeeds and returns a value
/// populated by the values yielded by `P`. Consumes the matched part of `F`. If `F` does not
/// succeed within the given range `R` this combinator will propagate any failure from `P`.
///
/// # Notes
///
/// * Will allocate depending on the `FromIterator` implementation.
/// * Will never yield more items than the upper bound of the range.
/// * If the last parser succeeds on the last input item then this combinator is still considered
///   incomplete unless the parser `F` matches or the lower bound has not been met.
#[inline]
pub fn many_till<'a, I, T, E, R, F, U, N, P, V>(i: Input<'a, I>, r: R, p: P, end: F) -> ParseResult<'a, I, T, E>
  where I: Copy,
        U: 'a,
        V: 'a,
        N: 'a,
        R: BoundedRange,
        T: FromIterator<U>,
        P: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, V, N> {
    BoundedRange::many_till(r, i, p, end)
}

#[cfg(test)]
mod test {
    use ParseResult;
    use parsers::{any, token};
    use primitives::input::*;
    use primitives::{IntoInner, State};

    use super::{
        many,
        many_till,
        skip_many,
    };

    #[test]
    fn many_range_full() {
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b""), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"a"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aa"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));

        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"b"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"ab"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aab"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b""), .., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"a"), .., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aa"), .., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"b"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"ab"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aab"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![b'a', b'a']));
    }

    #[test]
    fn many_range_to() {
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b""), ..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"a"), ..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b""), ..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"a"), ..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), vec![]));

        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b""), ..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"a"), ..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b""), ..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"a"), ..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), vec![]));

        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b""), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"a"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aa"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aaa"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), vec![b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"b"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"ab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b""), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"a"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aa"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"b"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"ab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aaab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"ab"), vec![b'a', b'a']));
    }

    #[test]
    fn many_range_from() {
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b""), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"a"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aa"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aaa"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));

        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"b"), 2.., |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"ab"), 2.., |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aab"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b""), 2.., any);
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"a"), 2.., any);
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aa"), 2.., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aaa"), 2.., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![b'a', b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"b"), 2.., |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"ab"), 2.., |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aab"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aaab"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![b'a', b'a', b'a']));
    }

    #[test]
    fn many_range() {
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b""), 0..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"a"), 0..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b""), 0..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"a"), 0..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), vec![]));

        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b""), 0..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"a"), 0..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b""), 0..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![]));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"a"), 0..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), vec![]));

        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b""), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"a"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aa"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aaa"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), vec![b'a', b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aaaa"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), vec![b'a', b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"b"), 2..4, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"ab"), 2..4, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aaab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![b'a', b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aaaab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"ab"), vec![b'a', b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b""), 2..4, any);
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"a"), 2..4, any);
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aa"), 2..4, any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aaa"), 2..4, any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![b'a', b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aaaa"), 2..4, any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), vec![b'a', b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"b"), 2..4, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"ab"), 2..4, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aaab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![b'a', b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aaaab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"ab"), vec![b'a', b'a', b'a']));
    }

    #[test]
    fn many_exact() {
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b""), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"a"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aa"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aaa"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), vec![b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"b"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"ab"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aab"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aaab"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"ab"), vec![b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b""), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"a"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aa"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aaa"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), vec![b'a', b'a']));

        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"b"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"ab"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aab"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), vec![b'a', b'a']));
        let r: ParseResult<_, Vec<_>, _> = many(new(END_OF_INPUT, b"aaab"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"ab"), vec![b'a', b'a']));
    }

    #[test]
    fn skip_range_full() {
        let r = skip_many(new(DEFAULT, b""), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"a"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"aa"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));

        let r = skip_many(new(DEFAULT, b"b"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));
        let r = skip_many(new(DEFAULT, b"ab"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));
        let r = skip_many(new(DEFAULT, b"aab"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));

        let r = skip_many(new(END_OF_INPUT, b""), .., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"a"), .., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"aa"), .., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));

        let r = skip_many(new(END_OF_INPUT, b"b"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
        let r = skip_many(new(END_OF_INPUT, b"ab"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
        let r = skip_many(new(END_OF_INPUT, b"aab"), .., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
    }

    #[test]
    fn skip_range_to() {
        let r = skip_many(new(DEFAULT, b""), ..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), ()));
        let r = skip_many(new(DEFAULT, b"a"), ..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), ()));
        let r = skip_many(new(END_OF_INPUT, b""), ..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"a"), ..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), ()));

        let r = skip_many(new(DEFAULT, b""), ..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), ()));
        let r = skip_many(new(DEFAULT, b"a"), ..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), ()));
        let r = skip_many(new(END_OF_INPUT, b""), ..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"a"), ..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), ()));

        let r = skip_many(new(DEFAULT, b""), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"a"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"aa"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), ()));
        let r = skip_many(new(DEFAULT, b"aaa"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), ()));

        let r = skip_many(new(DEFAULT, b"b"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));
        let r = skip_many(new(DEFAULT, b"ab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));
        let r = skip_many(new(DEFAULT, b"aab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));

        let r = skip_many(new(END_OF_INPUT, b""), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"a"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"aa"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));

        let r = skip_many(new(END_OF_INPUT, b"b"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
        let r = skip_many(new(END_OF_INPUT, b"ab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
        let r = skip_many(new(END_OF_INPUT, b"aab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
        let r = skip_many(new(END_OF_INPUT, b"aaab"), ..3, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"ab"), ()));
    }

    #[test]
    fn skip_range_from() {
        let r = skip_many(new(DEFAULT, b""), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"a"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"aa"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"aaa"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));

        let r = skip_many(new(DEFAULT, b"b"), 2.., |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(DEFAULT, b"ab"), 2.., |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(DEFAULT, b"aab"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));

        let r = skip_many(new(END_OF_INPUT, b""), 2.., any);
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(END_OF_INPUT, b"a"), 2.., any);
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(END_OF_INPUT, b"aa"), 2.., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"aaa"), 2.., any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));

        let r = skip_many(new(END_OF_INPUT, b"b"), 2.., |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(END_OF_INPUT, b"ab"), 2.., |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(END_OF_INPUT, b"aab"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
        let r = skip_many(new(END_OF_INPUT, b"aaab"), 2.., |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
    }

    #[test]
    fn skip_range() {
        let r = skip_many(new(DEFAULT, b""), 0..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), ()));
        let r = skip_many(new(DEFAULT, b"a"), 0..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), ()));
        let r = skip_many(new(END_OF_INPUT, b""), 0..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"a"), 0..0, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), ()));

        let r = skip_many(new(DEFAULT, b""), 0..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), ()));
        let r = skip_many(new(DEFAULT, b"a"), 0..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), ()));
        let r = skip_many(new(END_OF_INPUT, b""), 0..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"a"), 0..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), ()));

        let r = skip_many(new(DEFAULT, b""), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"a"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"aa"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"aaa"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), ()));
        let r = skip_many(new(DEFAULT, b"aaaa"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), ()));

        let r = skip_many(new(DEFAULT, b"b"), 2..4, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(DEFAULT, b"ab"), 2..4, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(DEFAULT, b"aab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));
        let r = skip_many(new(DEFAULT, b"aaab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));
        let r = skip_many(new(DEFAULT, b"aaaab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"ab"), ()));

        let r = skip_many(new(END_OF_INPUT, b""), 2..4, any);
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(END_OF_INPUT, b"a"), 2..4, any);
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(END_OF_INPUT, b"aa"), 2..4, any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"aaa"), 2..4, any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"aaaa"), 2..4, any);
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), ()));

        let r = skip_many(new(END_OF_INPUT, b"b"), 2..4, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(END_OF_INPUT, b"ab"), 2..4, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(END_OF_INPUT, b"aab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
        let r = skip_many(new(END_OF_INPUT, b"aaab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
        let r = skip_many(new(END_OF_INPUT, b"aaaab"), 2..4, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"ab"), ()));
    }

    #[test]
    fn skip_exact() {
        let r = skip_many(new(DEFAULT, b""), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"a"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(DEFAULT, b"aa"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b""), ()));
        let r = skip_many(new(DEFAULT, b"aaa"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"a"), ()));

        let r = skip_many(new(DEFAULT, b"b"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(DEFAULT, b"ab"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(DEFAULT, b"aab"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"b"), ()));
        let r = skip_many(new(DEFAULT, b"aaab"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"ab"), ()));

        let r = skip_many(new(END_OF_INPUT, b""), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(END_OF_INPUT, b"a"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Incomplete(1));
        let r = skip_many(new(END_OF_INPUT, b"aa"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b""), ()));
        let r = skip_many(new(END_OF_INPUT, b"aaa"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"a"), ()));

        let r = skip_many(new(END_OF_INPUT, b"b"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(END_OF_INPUT, b"ab"), 2, |i| token(i, b'a').map_err(|_| "token_err"));
        assert_eq!(r.into_inner(), State::Error(b"b", "token_err"));
        let r = skip_many(new(END_OF_INPUT, b"aab"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"b"), ()));
        let r = skip_many(new(END_OF_INPUT, b"aaab"), 2, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(END_OF_INPUT, b"ab"), ()));
    }

    #[test]
    #[should_panic]
    fn panic_many_range_lt() {
        let r: ParseResult<_, Vec<_>, _> = many(new(DEFAULT, b"aaaab"), 2..1, |i| token(i, b'a'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"ab"), vec![b'a', b'a', b'a']));
    }

    #[test]
    #[should_panic]
    fn panic_skip_many_range_lt() {
        assert_eq!(skip_many(new(DEFAULT, b"aaaab"), 2..1, |i| token(i, b'a')).into_inner(), State::Data(new(DEFAULT, b"ab"), ()));
    }

    #[test]
    #[should_panic]
    fn panic_many_till_range_lt() {
        let r: ParseResult<_, Vec<_>, _> = many_till(new(DEFAULT, b"aaaab"), 2..1, |i| token(i, b'a'), |i| token(i, b'b'));
        assert_eq!(r.into_inner(), State::Data(new(DEFAULT, b"ab"), vec![b'a', b'a', b'a']));
    }
}
