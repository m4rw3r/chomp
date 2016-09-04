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
//! let r: Result<Vec<_>, _> = parse_only(many(2..4, any), b"abcd");
//!
//! assert_eq!(r, Ok(vec![b'a', b'b', b'c']));
//! ```

use std::marker::PhantomData;
use std::iter::FromIterator;
use std::cmp::max;

use std::ops::{RangeFrom, RangeFull, RangeTo, Range};

use types::{Input, Parser, ThenParser};

/// Trait for applying a parser multiple times based on a range.
pub trait BoundedMany<I: Input, F, T, E> {
    /// The parser type returned by `many`.
    type ManyParser: Parser<I, Output=T, Error=E>;

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
    /// * Will never yield fewer items than the lower bound of the range.
    /// * Will only call the parser-constructor `F` once for each iteration, in order.
    /// * Use `combinators::bounded::many` instead of calling this trait method directly.
    #[inline]
    fn many(self, f: F) -> Self::ManyParser;
}

/// Trait for applying a parser multiple times based on a range, ignoring any output.
pub trait BoundedSkipMany<I: Input, F, E> {
    /// The parser type returned by `skip_many`.
    type SkipManyParser: Parser<I, Output=(), Error=E>;

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
    /// * Will never skip more items than the upper bound of the range.
    /// * Will never skip fewer items than the lower bound of the range.
    /// * Will only call the parser-constructor `F` once for each iteration, in order
    /// * Use `combinators::bounded::skip_many` instead of calling this trait method directly.
    #[inline]
    fn skip_many(self, F) -> Self::SkipManyParser;
}

/// Trait for applying a parser multiple times based on a range until another parser succeeds.
pub trait BoundedManyTill<I: Input, F, G, T, E> {
    /// The parser type returned by `many_till`.
    type ManyTillParser: Parser<I, Output=T, Error=E>;

    /// Applies the parser `F` multiple times until the parser `G` succeeds, collecting the values
    /// from `F` into a `T: FromIterator` Consumes the matched part of `G`. If `F` does not
    /// succeed within the given range `R` this combinator will propagate any failure from `G`.
    ///
    /// # Panics
    ///
    /// Will panic if the end of the range is smaller than the start of the range.
    ///
    /// # Notes
    ///
    /// * Will allocate depending on the `FromIterator` implementation.
    /// * Will never yield more items than the upper bound of the range.
    /// * Will never yield fewer items than the lower bound of the range.
    /// * Use `combinators::bounded::many_till` instead of calling this trait method directly.
    #[inline]
    fn many_till(self, F, G) -> Self::ManyTillParser;
}

many_iter!{
    doc:         "Parser iterating over a `Range`, created using `many(n..m, p)`.",
    struct_name: ManyRangeParser,
    state:       (usize, usize),

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
            self.data.0  = self.data.0.saturating_sub(1);
            // Can't overflow unless we forget to end before self.data.1 == 0
            self.data.1 -= 1;
        }
    }

    => result {
        // Got all occurrences of the parser
        // First state or reached max => do not restore to mark since it is from last
        // iteration
        (s, (0, 0), _, _)       => (s, Ok(result)),
        // Ok, last parser failed and we have reached minimum, we have iterated all.
        // Return remainder of buffer and the collected result
        (s, (0, _), m, Some(_)) => (s.restore(m), Ok(result)),
        // Did not reach minimum, propagate
        (s, (_, _), _, Some(e)) => (s, Err(e)),
        (_, _, _, None)         => unreachable!(),
    }
}

impl<I, F, T, P> BoundedMany<I, F, T, P::Error> for Range<usize>
  where I: Input,
        F: FnMut() -> P,
        T: FromIterator<P::Output>,
        P: Parser<I> {
    type ManyParser = ManyRangeParser<I, F, P, T>;

    #[inline]
    fn many(self, f: F) -> Self::ManyParser {
        // Range does not perform this assertion
        assert!(self.start <= self.end);

        ManyRangeParser {
            parser_ctor: f,
            // Range is closed on left side, open on right, ie. [start, end), but start <= end
            data:        (self.start, max(self.start, self.end.saturating_sub(1))),
            _i:          PhantomData,
            _t:          PhantomData,
            _p:          PhantomData,
        }
    }
}

/// Parser iterating over a `Range` discarding results, created using `skip_many(n..m, f)`.
#[derive(Debug)]
pub struct SkipManyRangeParser<I, F> {
    f:   F,
    max: usize,
    min: usize,
    _i:  PhantomData<I>
}

impl<I, F, P> Parser<I> for SkipManyRangeParser<I, F>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type Output = ();
    type Error  = P::Error;

    #[inline]
    fn parse(mut self, mut i: I) -> (I, Result<(), P::Error>) {
        loop {
            if self.max == 0 {
                break;
            }

            let m = i.mark();

            match (self.f)().parse(i) {
                (b, Ok(_))    => {
                    self.min  = self.min.saturating_sub(1);
                    // Can't overflow unless we do not quit when max == 0
                    self.max -= 1;

                    i = b
                },
                (b, Err(e))   => if self.min == 0 {
                    i = b.restore(m);

                    break;
                } else {
                    // Not enough iterations, propagate
                    return (b, Err(e));
                },
            }
        }

        (i, Ok(()))
    }
}

impl<I, F, P> BoundedSkipMany<I, F, P::Error> for Range<usize>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type SkipManyParser = SkipManyRangeParser<I, F>;

    #[inline]
    fn skip_many(self, f: F) -> Self::SkipManyParser {
        // Range does not perform this assertion
        assert!(self.start <= self.end);

        // Closed on left side, open on right
        SkipManyRangeParser {
            f: f,
            min: self.start,
            max: max(self.start, self.end.saturating_sub(1)),
            _i: PhantomData,
        }
    }
}

many_till_iter! {
    doc: "Parser iterating over a range and ending with a final parser, created by `many_till(n..m, ...)`",
    struct_name: ManyTillRangeParser,
    state:       (usize, usize),

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

                match (self.data.1, (self.end)().parse(i)) {
                    // We can always end
                    (_, (b, Ok(_)))  => {
                        self.buf   = Some(b);
                        self.state = EndStateTill::EndSuccess;

                        return None;
                    },
                    // We have reached end, end must match or it is an error
                    (0, (b, Err(e))) => {
                        self.buf   = Some(b);
                        self.state = EndStateTill::Error(From::from(e));

                        return None;
                    },
                    // Failed to end, restore and continue since we can parse more
                    (_, (b, Err(_))) => self.buf = Some(b.restore(m)),
                }
            }
        }
        on {
            self.data.0  = self.data.0.saturating_sub(1);
            // Can't overflow unless we forget to end before self.data.1 == 0
            self.data.1 -= 1;
        }
    }

    => result {
        // Got all occurrences of the parser
        (s, (0, _), EndStateTill::EndSuccess) => (s, Ok(result)),
        // Did not reach minimum or a failure, propagate
        (s, (_, _), EndStateTill::Error(e))   => (s, Err(e)),
        (_, (_, _), EndStateTill::Incomplete) => unreachable!(),
        // We cannot reach this since we only run the end test once we have reached the
        // minimum number of matches
        (_, (_, _), EndStateTill::EndSuccess) => unreachable!()
    }
}

impl<I: Input, F, G, P, Q, T> BoundedManyTill<I, F, G, T, P::Error> for Range<usize>
  where I: Input,
        F: FnMut() -> P,
        G: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error>,
        T: FromIterator<P::Output> {
    /// The parser type returned by `many_till`.
    type ManyTillParser = ManyTillRangeParser<I, F, G, P, Q, T>;

    #[inline]
    fn many_till(self, f: F, g: G) -> Self::ManyTillParser {
        // Range does not perform this assertion
        assert!(self.start <= self.end);

        ManyTillRangeParser {
            p_ctor: f,
            q_ctor: g,
            // Range is closed on left side, open on right, ie. [start, end), but start <= end
            data:   (self.start, max(self.start, self.end.saturating_sub(1))),
            _i:     PhantomData,
            _p:     PhantomData,
            _q:     PhantomData,
            _t:     PhantomData,
        }
    }
}

many_iter!{
    doc:         "Parser iterating over a `RangeFrom`, created using `many(n.., p)`.",
    struct_name: ManyRangeFromParser,
    // Inclusive
    state:       usize,

    size_hint(self) {
        (self.data, None)
    }

    next(self) {
        pre {}
        on  {
            self.data = self.data.saturating_sub(1);
        }
    }

    => result {
        // We got at least n items
        (s, 0, m, Some(_)) => (s.restore(m), Ok(result)),
        // Items still remaining, propagate
        (s, _, _, Some(e)) => (s, Err(e)),
        (_, _, _, None)    => unreachable!(),
    }
}

impl<I, F, T, P> BoundedMany<I, F, T, P::Error> for RangeFrom<usize>
  where I: Input,
        F: FnMut() -> P,
        T: FromIterator<P::Output>,
        P: Parser<I> {
    type ManyParser = ManyRangeFromParser<I, F, P, T>;

    #[inline]
    fn many(self, f: F) -> Self::ManyParser {
        ManyRangeFromParser {
            parser_ctor: f,
            // Range is closed on left side, open on right, ie. [start, end)
            data:        self.start,
            _i:          PhantomData,
            _t:          PhantomData,
            _p:          PhantomData,
        }
    }
}

/// Parser iterating over a `RangeFrom` discarding results, created using `skip_many(n.., f)`.
#[derive(Debug)]
pub struct SkipManyRangeFromParser<I, F> {
    f:   F,
    min: usize,
    _i:  PhantomData<I>
}

impl<I, F, P> Parser<I> for SkipManyRangeFromParser<I, F>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type Output = ();
    type Error  = P::Error;

    #[inline]
    fn parse(mut self, mut i: I) -> (I, Result<(), P::Error>) {
        loop {
            let m = i.mark();

            match (self.f)().parse(i) {
                (b, Ok(_))    => {
                    self.min  = self.min.saturating_sub(1);

                    i = b
                },
                (b, Err(e))   => if self.min == 0 {
                    i = b.restore(m);

                    break;
                } else {
                    // Not enough iterations, propagate
                    return (b, Err(e));
                },
            }
        }

        (i, Ok(()))
    }
}

impl<I, F, P> BoundedSkipMany<I, F, P::Error> for RangeFrom<usize>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type SkipManyParser = SkipManyRangeFromParser<I, F>;

    #[inline]
    fn skip_many(self, f: F) -> Self::SkipManyParser {
        // Closed on left side
        SkipManyRangeFromParser {
            f:   f,
            min: self.start,
            _i:  PhantomData,
        }
    }
}

many_till_iter! {
    doc: "Parser iterating over a `RangeFrom` and ending with a final parser, created by `many_till(n.., ...)`",
    struct_name: ManyTillRangeFromParser,
    state:       usize,

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
            self.data = self.data.saturating_sub(1);
        }
    }

    => result {
        // Got all occurrences of the parser
        (s, 0, EndStateTill::EndSuccess) => (s, Ok(result)),
        // Did not reach minimum or a failure, propagate
        (s, _, EndStateTill::Error(e))   => (s, Err(e)),
        (_, _, EndStateTill::Incomplete) => unreachable!(),
        // We cannot reach this since we only run the end test once we have reached the
        // minimum number of matches
        (_, _, EndStateTill::EndSuccess) => unreachable!()
    }
}

impl<I: Input, F, G, P, Q, T> BoundedManyTill<I, F, G, T, P::Error> for RangeFrom<usize>
  where I: Input,
        F: FnMut() -> P,
        G: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error>,
        T: FromIterator<P::Output> {
    /// The parser type returned by `many_till`.
    type ManyTillParser = ManyTillRangeFromParser<I, F, G, P, Q, T>;

    #[inline]
    fn many_till(self, f: F, g: G) -> Self::ManyTillParser {
        ManyTillRangeFromParser {
            p_ctor: f,
            q_ctor: g,
            // Range is closed on left side, unbounded on right
            data:   self.start,
            _i:     PhantomData,
            _p:     PhantomData,
            _q:     PhantomData,
            _t:     PhantomData,
        }
    }
}

many_iter!{
    doc:         "Parser iterating over a `RangeFull`, created using `many(.., p)`.",
    struct_name: ManyRangeFullParser,
    state:       (),

    size_hint(self) {
        (0, None)
    }

    next(self) {
        pre {}
        on  {}
    }

    => result {
        (s, (), m, Some(_)) => (s.restore(m), Ok(result)),
        (_, _, _, None)     => unreachable!(),
    }
}

impl<I, F, T, P> BoundedMany<I, F, T, P::Error> for RangeFull
  where I: Input,
        F: FnMut() -> P,
        T: FromIterator<P::Output>,
        P: Parser<I> {
    type ManyParser = ManyRangeFullParser<I, F, P, T>;

    #[inline]
    fn many(self, f: F) -> Self::ManyParser {
        ManyRangeFullParser {
            parser_ctor: f,
            data:        (),
            _i:          PhantomData,
            _t:          PhantomData,
            _p:          PhantomData,
        }
    }
}

/// Parser iterating over a `RangeFull` discarding results, created using `skip_many(.., f)`.
#[derive(Debug)]
pub struct SkipManyRangeFullParser<I, F> {
    f:   F,
    _i:  PhantomData<I>
}

impl<I, F, P> Parser<I> for SkipManyRangeFullParser<I, F>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type Output = ();
    type Error  = P::Error;

    #[inline]
    fn parse(mut self, mut i: I) -> (I, Result<(), P::Error>) {
        loop {
            let m = i.mark();

            match (self.f)().parse(i) {
                (b, Ok(_))  => i = b,
                (b, Err(_)) => {
                    i = b.restore(m);

                    break;
                },
            }
        }

        (i, Ok(()))
    }
}

impl<I, F, P> BoundedSkipMany<I, F, P::Error> for RangeFull
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type SkipManyParser = SkipManyRangeFullParser<I, F>;

    #[inline]
    fn skip_many(self, f: F) -> Self::SkipManyParser {
        SkipManyRangeFullParser {
            f:  f,
            _i: PhantomData,
        }
    }
}

many_till_iter! {
    doc: "Parser iterating over a `RangeFull` and ending with a final parser, created by `many_till(.., ...)`",
    struct_name: ManyTillRangeFullParser,
    state:       (),

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

    => result {
        (s, (), EndStateTill::EndSuccess) => (s, Ok(result)),
        (s, (), EndStateTill::Error(e))   => (s, Err(e)),
        // Nested parser incomplete, propagate if not at end
        (_, (), EndStateTill::Incomplete) => unreachable!()
    }
}

impl<I: Input, F, G, P, Q, T> BoundedManyTill<I, F, G, T, P::Error> for RangeFull
  where I: Input,
        F: FnMut() -> P,
        G: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error>,
        T: FromIterator<P::Output> {
    /// The parser type returned by `many_till`.
    type ManyTillParser = ManyTillRangeFullParser<I, F, G, P, Q, T>;

    #[inline]
    fn many_till(self, f: F, g: G) -> Self::ManyTillParser {
        ManyTillRangeFullParser {
            p_ctor: f,
            q_ctor: g,
            data:   (),
            _i:     PhantomData,
            _p:     PhantomData,
            _q:     PhantomData,
            _t:     PhantomData,
        }
    }
}

many_iter!{
    doc:         "Parser iterating over a `RangeTo`, created using `many(..n, p)`.",
    struct_name: ManyRangeToParser,
    // Exclusive range [0, end)
    state:       usize,

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

    => result {
        // First state or reached max => do not restore to mark since it is from last
        // iteration
        (s, 0, _, _)       => (s, Ok(result)),
        // Inside of range, never outside
        (s, _, m, Some(_)) => (s.restore(m), Ok(result)),
        (_, _, _, None)    => unreachable!(),
    }
}

impl<I, F, T, P> BoundedMany<I, F, T, P::Error> for RangeTo<usize>
  where I: Input,
        F: FnMut() -> P,
        T: FromIterator<P::Output>,
        P: Parser<I> {
    type ManyParser = ManyRangeToParser<I, F, P, T>;

    #[inline]
    fn many(self, f: F) -> Self::ManyParser {
        ManyRangeToParser {
            parser_ctor: f,
            // Exclusive range [0, end)
            data:        self.end.saturating_sub(1),
            _i:          PhantomData,
            _t:          PhantomData,
            _p:          PhantomData,
        }
    }
}

/// Parser iterating over a `RangeTo` discarding results, created using `skip_many(..n, f)`.
#[derive(Debug)]
pub struct SkipManyRangeToParser<I, F> {
    f:   F,
    max: usize,
    _i:  PhantomData<I>
}

impl<I, F, P> Parser<I> for SkipManyRangeToParser<I, F>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type Output = ();
    type Error  = P::Error;

    #[inline]
    fn parse(mut self, mut i: I) -> (I, Result<(), P::Error>) {
        loop {
            if self.max == 0 {
                break;
            }

            let m = i.mark();

            match (self.f)().parse(i) {
                (b, Ok(_))    => {
                    self.max -= 1;

                    i = b
                },
                // Always ok to end iteration
                (b, Err(_))   => {
                    i = b.restore(m);

                    break;
                },
            }
        }

        (i, Ok(()))
    }
}

impl<I, F, P> BoundedSkipMany<I, F, P::Error> for RangeTo<usize>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type SkipManyParser = SkipManyRangeToParser<I, F>;

    #[inline]
    fn skip_many(self, f: F) -> Self::SkipManyParser {
        // Open on right side
        SkipManyRangeToParser {
            f:   f,
            max: self.end.saturating_sub(1),
            _i:  PhantomData,
        }
    }
}

many_till_iter! {
    doc: "Parser iterating over a `RangeTo` and ending with a final parser, created by `many_till(..m, ...)`",
    struct_name: ManyTillRangeToParser,
    state:       usize,

    size_hint(self) {
        (0, Some(self.data))
    }

    next(self) {
        pre {
            // TODO: Remove the branches here (ie. take + unwrap)
            let i = self.buf.take().expect("Iter.buf was None");
            let m = i.mark();

            match (self.data, (self.end)().parse(i)) {
                // We can always end
                (_, (b, Ok(_)))  => {
                    self.buf   = Some(b);
                    self.state = EndStateTill::EndSuccess;

                    return None
                },
                // We have reached end, end must match or it is an error
                (0, (b, Err(e))) => {
                    self.buf   = Some(b);
                    self.state = EndStateTill::Error(From::from(e));

                    return None;
                },
                // Failed to end, restore and continue since we can parse more
                (_, (b, Err(_))) => self.buf = Some(b.restore(m)),
            }
        }
        on {
            self.data -= 1;
        }
    }

    => result {
        // Got all occurrences of the parser since we have no minimum bound
        (s, _, EndStateTill::EndSuccess) => (s, Ok(result)),
        // Did not reach minimum or a failure, propagate
        (s, _, EndStateTill::Error(e))   => (s, Err(e)),
        (_, _, EndStateTill::Incomplete) => unreachable!(),
    }
}

impl<I: Input, F, G, P, Q, T> BoundedManyTill<I, F, G, T, P::Error> for RangeTo<usize>
  where I: Input,
        F: FnMut() -> P,
        G: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error>,
        T: FromIterator<P::Output> {
    /// The parser type returned by `many_till`.
    type ManyTillParser = ManyTillRangeToParser<I, F, G, P, Q, T>;

    #[inline]
    fn many_till(self, f: F, g: G) -> Self::ManyTillParser {
        ManyTillRangeToParser {
            p_ctor: f,
            q_ctor: g,
            // [0, self.end)
            data:   self.end.saturating_sub(1),
            _i:     PhantomData,
            _p:     PhantomData,
            _q:     PhantomData,
            _t:     PhantomData,
        }
    }
}

many_iter!{
    doc:         "Parser iterating over a `usize`, created using `many(n, p)`.",
    struct_name: ManyExactParser,
    // Excatly self
    state:       usize,

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

    => result {
        // Got exact
        (s, 0, _, _)       => (s, Ok(result)),
        // We have got too few items, propagate error
        (s, _, _, Some(e)) => (s, Err(e)),
        (_, _, _, None)    => unreachable!(),
    }
}

impl<I, F, T, P> BoundedMany<I, F, T, P::Error> for usize
  where I: Input,
        F: FnMut() -> P,
        T: FromIterator<P::Output>,
        P: Parser<I> {
    type ManyParser = ManyExactParser<I, F, P, T>;

    #[inline]
    fn many(self, f: F) -> Self::ManyParser {
        ManyExactParser {
            parser_ctor: f,
            // Range is closed on left side, open on right, ie. [start, end)
            data:        self,
            _i:          PhantomData,
            _t:          PhantomData,
            _p:          PhantomData,
        }
    }
}

/// Parser iterating `n` times discarding results, created using `skip_many(n, f)`.
#[derive(Debug)]
pub struct SkipManyExactParser<I, F> {
    f:   F,
    n: usize,
    _i:  PhantomData<I>
}

impl<I, F, P> Parser<I> for SkipManyExactParser<I, F>
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type Output = ();
    type Error  = P::Error;

    #[inline]
    fn parse(mut self, mut i: I) -> (I, Result<(), P::Error>) {
        loop {
            if self.n == 0 {
                break;
            }

            match (self.f)().parse(i) {
                (b, Ok(_))    => {
                    self.n -= 1;

                    i = b
                },
                (b, Err(e))   => if self.n == 0 {
                    unreachable!();
                } else {
                    // Not enough iterations, propagate
                    return (b, Err(e));
                },
            }
        }

        (i, Ok(()))
    }
}

impl<I, F, P> BoundedSkipMany<I, F, P::Error> for usize
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I> {
    type SkipManyParser = SkipManyExactParser<I, F>;

    #[inline]
    fn skip_many(self, f: F) -> Self::SkipManyParser {
        SkipManyExactParser {
            f:  f,
            n:  self,
            _i: PhantomData,
        }
    }
}

many_till_iter! {
    doc: "Parser iterating `usize` times and ending with a final parser, created by `many_till(n, ...)`",
    struct_name: ManyTillExactParser,
    state:       usize,

    size_hint(self) {
        (self.data, Some(self.data))
    }

    next(self) {
        pre {
            if self.data == 0 {
                // Reached exact, MUST end here:

                // TODO: Remove the branches here (ie. take + unwrap)
                let i = self.buf.take().expect("Iter.buf was None");

                match (self.end)().parse(i) {
                    (b, Ok(_)) => {
                        self.buf   = Some(b);
                        self.state = EndStateTill::EndSuccess;
                    },
                    // Failed to end, restore and continue
                    (b, Err(e))      => {
                        self.buf   = Some(b);
                        self.state = EndStateTill::Error(e);
                    },
                }

                return None;
            }
        }
        on {
            self.data -= 1;
        }
    }

    => result {
        // Got all occurrences of the parser
        (s, 0, EndStateTill::EndSuccess) => (s, Ok(result)),
        // Did not reach minimum or a failure, propagate
        (s, _, EndStateTill::Error(e))   => (s, Err(e)),
        (_, _, EndStateTill::Incomplete) => unreachable!(),
        // We cannot reach this since we only run the end test once we have reached the
        // minimum number of matches
        (_, _, EndStateTill::EndSuccess) => unreachable!(),
    }
}

impl<I: Input, F, G, P, Q, T> BoundedManyTill<I, F, G, T, P::Error> for usize
  where I: Input,
        F: FnMut() -> P,
        G: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error>,
        T: FromIterator<P::Output> {
    /// The parser type returned by `many_till`.
    type ManyTillParser = ManyTillExactParser<I, F, G, P, Q, T>;

    #[inline]
    fn many_till(self, f: F, g: G) -> Self::ManyTillParser {
        ManyTillExactParser {
            p_ctor: f,
            q_ctor: g,
            data:   self,
            _i:     PhantomData,
            _p:     PhantomData,
            _q:     PhantomData,
            _t:     PhantomData,
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
/// * Will never yield fewer items than the lower bound of the range.
/// * Will only call the parser-constructor `F` once for each iteration, in order
#[inline]
pub fn many<I, F, P, T, R>(r: R, f: F) -> R::ManyParser
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I>,
        T: FromIterator<P::Output>,
        R: BoundedMany<I, F, T, P::Error> {
    BoundedMany::many(r, f)
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
/// * Will never parse more items than the upper bound of the range.
/// * Will never parse fewer items than the lower bound of the range.
/// * Will only call the parser-constructor `F` once for each iteration, in order
#[inline]
pub fn skip_many<I, F, P, R>(r: R, f: F) -> R::SkipManyParser
  where I: Input,
        F: FnMut() -> P,
        P: Parser<I>,
        R: BoundedSkipMany<I, F, P::Error> {
    BoundedSkipMany::skip_many(r, f)
}

/// Applies the parser `F` multiple times until the parser `G` succeeds, collecting the values
/// from `F` into a `T: FromIterator` Consumes the matched part of `G`. If `F` does not
/// succeed within the given range `R` this combinator will propagate any failure from `G`.
///
/// # Panics
///
/// Will panic if the end of the range is smaller than the start of the range.
///
/// # Notes
///
/// * Will allocate depending on the `FromIterator` implementation.
/// * Will never yield more items than the upper bound of the range.
/// * Will never yield fewer items than the lower bound of the range.
/// * Use `combinators::bounded::many_till` instead of calling this trait method directly.
#[inline]
pub fn many_till<I, F, G, P, Q, T, R>(r: R, p: F, end: G) -> R::ManyTillParser
  where I: Input,
        //E: From<N>,
        F: FnMut() -> P,
        G: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error>,
        T: FromIterator<P::Output>,
        R: BoundedManyTill<I, F, G, T, P::Error> {
    BoundedManyTill::many_till(r, p, end)
}

/// Applies the parser `p` multiple times, separated by the parser `sep` and returns a value
/// populated with the values yielded by `p`. If the number of items yielded by `p` does not fall
/// into the range `r` and the separator or parser registers error failure is propagated.
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
// TODO: look at the From<N>
pub fn sep_by<I, T, F, G, P, Q, R>(r: R, f: F, sep: G) -> R::ManyParser
  where I: Input,
        T: FromIterator<P::Output>,
        F: FnMut() -> P,
        G: FnMut() -> Q,
        // E: From<N>,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error>,
        R: BoundedMany<I, SepByInnerParserCtor<I, F, G>, T, P::Error> {
    BoundedMany::many(r, SepByInnerParserCtor {
        item: false,
        f:    f,
        sep:  sep,
        _i:   PhantomData,
    })
}

/// Constructor for the inner parser used by `sep_by`.
///
/// This type is created internally by `sep_by` to construct the appropriate parser from a
/// `BoundedMany` implementation providing the iteration.
// Due to the requirement of BoundedMany to be able to specify a concrete type for the function (F)
// parameter we need to have a type we can describe and not a closure for the type of the sep-by
// inner parser
// TODO: Implement as a trait for `ParserConstructor`?
#[derive(Debug)]
pub struct SepByInnerParserCtor<I, F, S> {
    item: bool,
    f:    F,
    sep:  S,
    _i:   PhantomData<I>,
}

impl<I, F, S, P, Q> FnOnce<()> for SepByInnerParserCtor<I, F, S>
  where I: Input,
        F: FnMut() -> P,
        S: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error> {
    type Output = ThenParser<I, MaybeAParser<Q>, P>;

    extern "rust-call" fn call_once(self, _: ()) -> Self::Output {
        unimplemented!()
    }
}

impl<I, F, S, P, Q> FnMut<()> for SepByInnerParserCtor<I, F, S>
  where I: Input,
        F: FnMut() -> P,
        S: FnMut() -> Q,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error> {
    extern "rust-call" fn call_mut(&mut self, _: ()) -> Self::Output {
        if self.item {
            MaybeAParser::parser((self.sep)())
        }
        else {
            self.item = true;

            MaybeAParser::none()
        }.then((self.f)())
    }
}

// TODO: More doc, and probably move
/// Parser required to unify code of the style of Option<P> to allow for stack-allocation.
#[derive(Debug)]
pub struct MaybeAParser<P>(Option<P>);

impl<P> MaybeAParser<P> {
    /// Creates a new wrapper containing a parser to be run.
    pub fn parser<I>(p: P) -> MaybeAParser<P>
      where I: Input,
            P: Parser<I> {
        MaybeAParser(Some(p))
    }

    /// Creates an empty wrapper plassing the success value.
    pub fn none() -> MaybeAParser<P> {
        MaybeAParser(None)
    }
}

impl<I, P> Parser<I> for MaybeAParser<P>
  where I: Input,
        P: Parser<I> {
    type Output = Option<P::Output>;
    type Error  = P::Error;

    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        match self.0 {
            Some(p) => match p.parse(i) {
                (r, Ok(t))  => (r, Ok(Some(t))),
                (r, Err(e)) => (r, Err(e)),
            },
            None    => (i, Ok(None)),
        }
    }
}

#[cfg(test)]
mod test {
    use parsers::{Error, any, token, string};
    use types::{Parser, ret};

    use super::{
        many,
        many_till,
        skip_many,
    };

    #[test]
    fn many_range_full() {
        let r = many(.., || token(b'a')); assert_eq!(r.parse(&b"b"[..]),   (&b"b"[..], Ok(vec![])));
        let r = many(.., || token(b'a')); assert_eq!(r.parse(&b"ab"[..]),  (&b"b"[..], Ok(vec![b'a'])));
        let r = many(.., || token(b'a')); assert_eq!(r.parse(&b"aab"[..]), (&b"b"[..], Ok(vec![b'a', b'a'])));

        let r = many(.., any); assert_eq!(r.parse(&b""[..]),   (&b""[..], Ok(vec![])));
        let r = many(.., any); assert_eq!(r.parse(&b"a"[..]),  (&b""[..], Ok(vec![b'a'])));
        let r = many(.., any); assert_eq!(r.parse(&b"aa"[..]), (&b""[..], Ok(vec![b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r = many(.., || string(b"ab")); assert_eq!(r.parse(&b"abac"[..]), (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r = many(.., || string(b"ab")); assert_eq!(r.parse(&b"abac"[..]), (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r = many(.., || string(b"ab")); assert_eq!(r.parse(&b"aba"[..]),  (&b"a"[..],  Ok(vec![&b"ab"[..]])));
    }

    #[test]
    fn many_range_to() {
        let r = many(..0, || token(b'a')); assert_eq!(r.parse(&b""[..]),  (&b""[..], Ok(vec![])));
        let r = many(..0, || token(b'a')); assert_eq!(r.parse(&b"a"[..]), (&b"a"[..], Ok(vec![])));

        let r = many(..1, || token(b'a')); assert_eq!(r.parse(&b""[..]),   (&b""[..], Ok(vec![])));
        let r = many(..1, || token(b'a')); assert_eq!(r.parse(&b"a"[..]),  (&b"a"[..], Ok(vec![])));

        let r = many(..3, || token(b'a')); assert_eq!(r.parse(&b""[..]),     (&b""[..], Ok(vec![])));
        let r = many(..3, || token(b'a')); assert_eq!(r.parse(&b"a"[..]),    (&b""[..], Ok(vec![b'a'])));
        let r = many(..3, || token(b'a')); assert_eq!(r.parse(&b"aa"[..]),   (&b""[..], Ok(vec![b'a', b'a'])));
        let r = many(..3, || token(b'a')); assert_eq!(r.parse(&b"aaa"[..]),  (&b"a"[..], Ok(vec![b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r = many(..3, || string(b"ab")); assert_eq!(r.parse(&b"abac"[..]),  (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r = many(..3, || string(b"ab")); assert_eq!(r.parse(&b"abac"[..]),  (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r = many(..3, || string(b"ab")); assert_eq!(r.parse(&b"aba"[..]),   (&b"a"[..], Ok(vec![&b"ab"[..]])));
    }

    #[test]
    fn many_range_to_limit() {
        // Test infinite
        let r: (_, Result<Vec<_>, ()>) = many(..4, || ret(b'a')).parse(&b"bbbbbbbbbb"[..]);
        assert_eq!(r, (&b"bbbbbbbbbb"[..], Ok(vec![b'a', b'a', b'a'])));
    }

    #[test]
    fn many_range_from() {
        let r: (_, Result<Vec<_>, _>) = many(0.., || token(b'a')).parse(&b""[..]);    assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many(0.., || token(b'a')).parse(&b"a"[..]);   assert_eq!(r, (&b""[..], Ok(vec![b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(0.., || token(b'a')).parse(&b"aa"[..]);  assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(0.., || token(b'a')).parse(&b"aaa"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a', b'a'])));

        let r: (_, Result<Vec<_>, _>) = many(2.., || token(b'a')).parse(&b""[..]);    assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2.., || token(b'a')).parse(&b"a"[..]);   assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2.., || token(b'a')).parse(&b"aa"[..]);  assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(2.., || token(b'a')).parse(&b"aaa"[..]); assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a', b'a'])));

        let r: (_, Result<Vec<_>, _>) = many(2.., || token(b'a')).parse(&b"b"[..]);    assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2.., || token(b'a')).parse(&b"ab"[..]);   assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2.., || token(b'a')).parse(&b"aab"[..]);  assert_eq!(r, (&b"b"[..], Ok(vec![b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(2.., || token(b'a')).parse(&b"aaab"[..]); assert_eq!(r, (&b"b"[..], Ok(vec![b'a', b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r = many(2.., || string(b"ab")); assert_eq!(r.parse(&b"ababac"[..]),  (&b"ac"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r = many(2.., || string(b"ab")); assert_eq!(r.parse(&b"ababac"[..]),  (&b"ac"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r = many(2.., || string(b"ab")); assert_eq!(r.parse(&b"ababa"[..]),   (&b"a"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
    }

    #[test]
    fn many_range() {
        let r = many(0..0, || token(b'a')); assert_eq!(r.parse(&b""[..]),   (&b""[..], Ok(vec![])));
        let r = many(0..0, || token(b'a')); assert_eq!(r.parse(&b"a"[..]),  (&b"a"[..], Ok(vec![])));
        let r = many(0..0, || token(b'a')); assert_eq!(r.parse(&b""[..]),   (&b""[..], Ok(vec![])));
        let r = many(0..0, || token(b'a')); assert_eq!(r.parse(&b"a"[..]),  (&b"a"[..], Ok(vec![])));

        let r: (_, Result<Vec<_>, _>) = many(2..2, || token(b'a')).parse(&b""[..])    ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2..2, || token(b'a')).parse(&b"a"[..])   ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2..2, || token(b'a')).parse(&b"aa"[..])  ; assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(2..2, || token(b'a')).parse(&b"aaa"[..])  ; assert_eq!(r, (&b"a"[..], Ok(vec![b'a', b'a'])));

        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b""[..])    ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b"a"[..])   ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b"aa"[..])  ; assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b"aaa"[..]) ; assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b"aaaa"[..]); assert_eq!(r, (&b"a"[..], Ok(vec![b'a', b'a', b'a'])));

        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b"b"[..])    ; assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b"ab"[..])   ; assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b"aab"[..])  ; assert_eq!(r, (&b"b"[..], Ok(vec![b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b"aaab"[..]) ; assert_eq!(r, (&b"b"[..], Ok(vec![b'a', b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(2..4, || token(b'a')).parse(&b"aaaab"[..]); assert_eq!(r, (&b"ab"[..], Ok(vec![b'a', b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r = many(1..3, || string(b"ab")); assert_eq!(r.parse(&b"abac"[..]),    (&b"ac"[..], Ok(vec![&b"ab"[..]])));
        let r = many(1..3, || string(b"ab")); assert_eq!(r.parse(&b"ababac"[..]),  (&b"ac"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
    }

    #[test]
    fn many_range_limit() {
        // Test infinite
        let r: (_, Result<Vec<_>, ()>) = many(2..4, || ret(b'a')).parse(&b"bbbbbbbbbb"[..]);
        assert_eq!(r, (&b"bbbbbbbbbb"[..], Ok(vec![b'a', b'a', b'a'])));
    }

    #[test]
    fn many_exact() {
        let r = many(0, || token(b'a')); assert_eq!(r.parse(&b""[..]),     (&b""[..], Ok(vec![])));
        let r = many(0, || token(b'a')); assert_eq!(r.parse(&b"a"[..]),    (&b"a"[..], Ok(vec![])));
        let r = many(0, || token(b'a')); assert_eq!(r.parse(&b"aa"[..]),   (&b"aa"[..], Ok(vec![])));

        let r: (_, Result<Vec<_>, _>) = many(2, || token(b'a')).parse(&b""[..])    ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2, || token(b'a')).parse(&b"a"[..])   ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2, || token(b'a')).parse(&b"aa"[..])  ; assert_eq!(r, (&b""[..], Ok(vec![b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(2, || token(b'a')).parse(&b"aaa"[..]) ; assert_eq!(r, (&b"a"[..], Ok(vec![b'a', b'a'])));

        let r: (_, Result<Vec<_>, _>) = many(2, || token(b'a')).parse(&b"b"[..])    ; assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2, || token(b'a')).parse(&b"ab"[..])   ; assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many(2, || token(b'a')).parse(&b"aab"[..])  ; assert_eq!(r, (&b"b"[..], Ok(vec![b'a', b'a'])));
        let r: (_, Result<Vec<_>, _>) = many(2, || token(b'a')).parse(&b"aaab"[..]) ; assert_eq!(r, (&b"ab"[..], Ok(vec![b'a', b'a'])));

        // Test where we error inside of the inner parser
        let r: (_, Result<Vec<_>, _>) = many(2, || string(b"ab")).parse(&b"abac"[..])   ; assert_eq!(r, (&b"c"[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many(2, || string(b"ab")).parse(&b"ababa"[..])  ; assert_eq!(r, (&b"a"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many(2, || string(b"ab")).parse(&b"abac"[..])   ; assert_eq!(r, (&b"c"[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many(2, || string(b"ab")).parse(&b"ababac"[..]) ; assert_eq!(r, (&b"ac"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many(2, || string(b"ab")).parse(&b"ababa"[..])  ; assert_eq!(r, (&b"a"[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
    }

    #[test]
    fn many_till_range_full() {
        let r: (_, Result<Vec<_>, _>) = many_till(.., || string(b"ab"), || string(b"ac")).parse(&b""[..]);        assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(.., || string(b"ab"), || string(b"ac")).parse(&b"ac"[..]);      assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(.., || string(b"ab"), || string(b"ac")).parse(&b"abac"[..]);    assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(.., || string(b"ab"), || string(b"ac")).parse(&b"ababac"[..]);  assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(.., || string(b"ab"), || string(b"ac")).parse(&b"ababab"[..]);  assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(.., || string(b"ab"), || string(b"ac")).parse(&b"abababa"[..]); assert_eq!(r, (&b""[..], Err(Error::expected(b'b'))));
    }

    #[test]
    fn many_till_range_from() {
        let r: (_, Result<Vec<_>, _>) = many_till(0.., || string(b"ab"), || string(b"ac")).parse(&b""[..])        ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0.., || string(b"ab"), || string(b"ac")).parse(&b"a"[..])       ; assert_eq!(r, (&b""[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0.., || string(b"ab"), || string(b"ac")).parse(&b"ab"[..])      ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0.., || string(b"ab"), || string(b"ac")).parse(&b"ac"[..])      ; assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(1.., || string(b"ab"), || string(b"ac")).parse(&b"ac"[..])      ; assert_eq!(r, (&b"c"[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0.., || string(b"ab"), || string(b"ac")).parse(&b"abac"[..])    ; assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(1.., || string(b"ab"), || string(b"ac")).parse(&b"abac"[..])    ; assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(2.., || string(b"ab"), || string(b"ac")).parse(&b"abac"[..])    ; assert_eq!(r, (&b"c"[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2.., || string(b"ab"), || string(b"ac")).parse(&b"ababac"[..])  ; assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(2.., || string(b"ab"), || string(b"ac")).parse(&b"ababab"[..])  ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2.., || string(b"ab"), || string(b"ac")).parse(&b"abababa"[..]) ; assert_eq!(r, (&b""[..], Err(Error::expected(b'b'))));
    }

    #[test]
    fn many_till_range_to() {
        let r: (_, Result<Vec<_>, _>) = many_till(..0, || string(b"ab"), || string(b"ac")).parse(&b""[..])         ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(..0, || string(b"ab"), || string(b"ac")).parse(&b"b"[..])        ; assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(..0, || string(b"ab"), || string(b"ac")).parse(&b"a"[..])        ; assert_eq!(r, (&b""[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(..0, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..])       ; assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(..1, || string(b"ab"), || string(b"ac")).parse(&b""[..])         ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(..1, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..])       ; assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(..2, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..])     ; assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(..3, || string(b"ab"), || string(b"ac")).parse(&b""[..])         ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(..3, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..])       ; assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(..3, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..])     ; assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(..3, || string(b"ab"), || string(b"ac")).parse(&b"ababac"[..])   ; assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(..3, || string(b"ab"), || string(b"ac")).parse(&b"abababac"[..]) ; assert_eq!(r, (&b"bac"[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(..3, || string(b"ab"), || string(b"ac")).parse(&b"ababab"[..])   ; assert_eq!(r, (&b"b"[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(..3, || string(b"ab"), || string(b"ac")).parse(&b"ababa"[..])    ; assert_eq!(r, (&b""[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(..3, || string(b"ab"), || string(b"ac")).parse(&b"abababa"[..])  ; assert_eq!(r, (&b"ba"[..], Err(Error::expected(b'c'))));
    }

    #[test]
    fn many_till_range() {
        let r: (_, Result<Vec<_>, _>) = many_till(0..0, || string(b"ab"), || string(b"ac")).parse(&b""[..]);   assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..0, || string(b"ab"), || string(b"cd")).parse(&b""[..]);   assert_eq!(r, (&b""[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..0, || string(b"ab"), || string(b"ac")).parse(&b"a"[..]);  assert_eq!(r, (&b""[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..0, || string(b"ab"), || string(b"ac")).parse(&b"ab"[..]); assert_eq!(r, (&b"b"[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..0, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..]); assert_eq!(r, (&b""[..], Ok(vec![])));

        let r: (_, Result<Vec<_>, _>) = many_till(0..1, || string(b"ab"), || string(b"ac")).parse(&b""[..]);         assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..1, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..]);       assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(0..1, || string(b"ab"), || string(b"ac")).parse(&b"ab"[..]);       assert_eq!(r, (&b"b"[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..1, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..]);     assert_eq!(r, (&b"bac"[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..2, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..]);       assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(0..2, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..]);     assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(0..3, || string(b"ab"), || string(b"ac")).parse(&b""[..]);         assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..3, || string(b"ab"), || string(b"ac")).parse(&b"a"[..]);        assert_eq!(r, (&b""[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..3, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..]);       assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(0..3, || string(b"ab"), || string(b"ac")).parse(&b"abc"[..]);      assert_eq!(r, (&b"c"[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..3, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..]);     assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(0..3, || string(b"ab"), || string(b"ac")).parse(&b"ababac"[..]);   assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(0..3, || string(b"ab"), || string(b"ac")).parse(&b"abababac"[..]); assert_eq!(r, (&b"bac"[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..3, || string(b"ab"), || string(b"ac")).parse(&b"ababa"[..]);    assert_eq!(r, (&b""[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0..3, || string(b"ab"), || string(b"ac")).parse(&b"abababa"[..]);  assert_eq!(r, (&b"ba"[..], Err(Error::expected(b'c'))));

        let r: (_, Result<Vec<_>, _>) = many_till(1..3, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..]);   assert_eq!(r, (&b"c"[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(1..3, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..]); assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(2..3, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..]); assert_eq!(r, (&b"c"[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2..3, || string(b"ab"), || string(b"ac")).parse(&b"ababac"[..]); assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(2..2, || string(b"ab"), || string(b"ac")).parse(&b"ababac"[..]); assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
    }

    #[test]
    fn many_till_exact() {
        let r: (_, Result<Vec<_>, _>) = many_till(0, || string(b"ab"), || string(b"ac")).parse(&b""[..]);        assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0, || string(b"ab"), || string(b"ac")).parse(&b"a"[..]);       assert_eq!(r, (&b""[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..]);      assert_eq!(r, (&b""[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(0, || string(b"ab"), || string(b"ac")).parse(&b"aca"[..]);     assert_eq!(r, (&b"a"[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(0, || string(b"ab"), || string(b"ac")).parse(&b"acab"[..]);    assert_eq!(r, (&b"ab"[..], Ok(vec![])));
        let r: (_, Result<Vec<_>, _>) = many_till(0, || string(b"ab"), || string(b"ac")).parse(&b"ab"[..]);      assert_eq!(r, (&b"b"[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(0, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..]);    assert_eq!(r, (&b"bac"[..], Err(Error::expected(b'c'))));

        let r: (_, Result<Vec<_>, _>) = many_till(1, || string(b"ab"), || string(b"ac")).parse(&b""[..]);        assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(1, || string(b"ab"), || string(b"ac")).parse(&b"a"[..]);       assert_eq!(r, (&b""[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(1, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..]);      assert_eq!(r, (&b"c"[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(1, || string(b"ab"), || string(b"ac")).parse(&b"ab"[..]);      assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(1, || string(b"ab"), || string(b"ac")).parse(&b"aba"[..]);     assert_eq!(r, (&b""[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(1, || string(b"ab"), || string(b"ac")).parse(&b"abab"[..]);    assert_eq!(r, (&b"b"[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(1, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..]);    assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..]])));

        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b""[..]);         assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"a"[..]);        assert_eq!(r, (&b""[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"ac"[..]);       assert_eq!(r, (&b"c"[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"ab"[..]);       assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"aba"[..]);      assert_eq!(r, (&b""[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"abab"[..]);     assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"abac"[..]);     assert_eq!(r, (&b"c"[..], Err(Error::expected(b'b'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"ababa"[..]);    assert_eq!(r, (&b""[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"ababac"[..]);   assert_eq!(r, (&b""[..], Ok(vec![&b"ab"[..], &b"ab"[..]])));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"ababab"[..]);   assert_eq!(r, (&b"b"[..], Err(Error::expected(b'c'))));
        let r: (_, Result<Vec<_>, _>) = many_till(2, || string(b"ab"), || string(b"ac")).parse(&b"abababac"[..]); assert_eq!(r, (&b"bac"[..], Err(Error::expected(b'c'))));
    }

    #[test]
    fn skip_range_full() {
        let r = skip_many(.., || token(b'a')); assert_eq!(r.parse(&b""[..]),   (&b""[..], Ok(())));
        let r = skip_many(.., || token(b'a')); assert_eq!(r.parse(&b"a"[..]),  (&b""[..], Ok(())));
        let r = skip_many(.., || token(b'a')); assert_eq!(r.parse(&b"aa"[..]), (&b""[..], Ok(())));

        let r = skip_many(.., || token(b'a')); assert_eq!(r.parse(&b"b"[..])   , (&b"b"[..], Ok(())));
        let r = skip_many(.., || token(b'a')); assert_eq!(r.parse(&b"ab"[..])  , (&b"b"[..], Ok(())));
        let r = skip_many(.., || token(b'a')); assert_eq!(r.parse(&b"aab"[..]) , (&b"b"[..], Ok(())));
    }

    #[test]
    fn skip_range_to() {
        let r = skip_many(..0, || token(b'a')); assert_eq!(r.parse(&b""[..] ), (&b""[..], Ok(())));
        let r = skip_many(..0, || token(b'a')); assert_eq!(r.parse(&b"b"[..] ), (&b"b"[..], Ok(())));
        let r = skip_many(..0, || token(b'a')); assert_eq!(r.parse(&b"a"[..]), (&b"a"[..], Ok(())));

        let r = skip_many(..1, || token(b'a')); assert_eq!(r.parse(&b""[..] ), (&b""[..], Ok(())));
        let r = skip_many(..1, || token(b'a')); assert_eq!(r.parse(&b"a"[..]), (&b"a"[..], Ok(())));

        let r = skip_many(..2, || token(b'a')); assert_eq!(r.parse(&b""[..] ), (&b""[..], Ok(())));
        let r = skip_many(..2, || token(b'a')); assert_eq!(r.parse(&b"a"[..]), (&b""[..], Ok(())));

        let r = skip_many(..3, || token(b'a')); assert_eq!(r.parse(&b""[..]   ), (&b""[..], Ok(())));
        let r = skip_many(..3, || token(b'a')); assert_eq!(r.parse(&b"a"[..]  ), (&b""[..], Ok(())));
        let r = skip_many(..3, || token(b'a')); assert_eq!(r.parse(&b"aa"[..] ), (&b""[..], Ok(())));
        let r = skip_many(..3, || token(b'a')); assert_eq!(r.parse(&b"aaa"[..]), (&b"a"[..], Ok(())));

        let r = skip_many(..3, || token(b'a')); assert_eq!(r.parse(&b"b"[..]   ), (&b"b"[..], Ok(())));
        let r = skip_many(..3, || token(b'a')); assert_eq!(r.parse(&b"ab"[..]  ), (&b"b"[..], Ok(())));
        let r = skip_many(..3, || token(b'a')); assert_eq!(r.parse(&b"aab"[..] ), (&b"b"[..], Ok(())));
        let r = skip_many(..3, || token(b'a')); assert_eq!(r.parse(&b"aaab"[..]), (&b"ab"[..], Ok(())));
    }

    #[test]
    fn skip_range_from() {
        let r = skip_many(0.., || token(b'a')); assert_eq!(r.parse(&b""[..] ), (&b""[..], Ok(())));
        let r = skip_many(0.., || token(b'a')); assert_eq!(r.parse(&b"a"[..] ), (&b""[..], Ok(())));
        let r = skip_many(0.., || token(b'a')); assert_eq!(r.parse(&b"aa"[..] ), (&b""[..], Ok(())));

        let r = skip_many(2.., || token(b'a')); assert_eq!(r.parse(&b""[..]   ), (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(2.., || token(b'a')); assert_eq!(r.parse(&b"a"[..]  ), (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(2.., || token(b'a')); assert_eq!(r.parse(&b"aa"[..] ), (&b""[..], Ok(())));
        let r = skip_many(2.., || token(b'a')); assert_eq!(r.parse(&b"aaa"[..]), (&b""[..], Ok(())));

        let r = skip_many(2.., || token(b'a')); assert_eq!(r.parse(&b"b"[..]   ), (&b"b"[..], Err(Error::expected(b'a'))));
        let r = skip_many(2.., || token(b'a')); assert_eq!(r.parse(&b"ab"[..]  ), (&b"b"[..], Err(Error::expected(b'a'))));
        let r = skip_many(2.., || token(b'a')); assert_eq!(r.parse(&b"aab"[..] ), (&b"b"[..], Ok(())));
        let r = skip_many(2.., || token(b'a')); assert_eq!(r.parse(&b"aaab"[..]), (&b"b"[..], Ok(())));
    }

    #[test]
    fn skip_range() {
        let r = skip_many(0..0, || token(b'a')); assert_eq!(r.parse(&b""[..] ), (&b""[..], Ok(())));
        let r = skip_many(0..0, || token(b'a')); assert_eq!(r.parse(&b"a"[..]), (&b"a"[..], Ok(())));

        let r = skip_many(2..2, || token(b'a')).parse(&b""[..]    ) ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(2..2, || token(b'a')).parse(&b"a"[..]   ) ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(2..2, || token(b'a')).parse(&b"aa"[..]  ) ; assert_eq!(r, (&b""[..], Ok(())));
        let r = skip_many(2..2, || token(b'a')).parse(&b"aaa"[..] ) ; assert_eq!(r, (&b"a"[..], Ok(())));

        let r = skip_many(2..4, || token(b'a')).parse(&b""[..]    ) ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(2..4, || token(b'a')).parse(&b"a"[..]   ) ; assert_eq!(r, (&b""[..], Err(Error::expected(b'a'))));
        let r = skip_many(2..4, || token(b'a')).parse(&b"aa"[..]  ) ; assert_eq!(r, (&b""[..], Ok(())));
        let r = skip_many(2..4, || token(b'a')).parse(&b"aaa"[..] ) ; assert_eq!(r, (&b""[..], Ok(())));
        let r = skip_many(2..4, || token(b'a')).parse(&b"aaaa"[..]) ; assert_eq!(r, (&b"a"[..], Ok(())));

        let r = skip_many(2..4, || token(b'a')).parse(&b"b"[..]    ); assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));
        let r = skip_many(2..4, || token(b'a')).parse(&b"ab"[..]   ); assert_eq!(r, (&b"b"[..], Err(Error::expected(b'a'))));
        let r = skip_many(2..4, || token(b'a')).parse(&b"aab"[..]  ); assert_eq!(r, (&b"b"[..], Ok(())));
        let r = skip_many(2..4, || token(b'a')).parse(&b"aaab"[..] ); assert_eq!(r, (&b"b"[..], Ok(())));
        let r = skip_many(2..4, || token(b'a')).parse(&b"aaaab"[..]); assert_eq!(r, (&b"ab"[..], Ok(())));
    }

    #[test]
    fn skip_exact() {
        let r = skip_many(0, || token(b'a')).parse(&b""[..]    ); assert_eq!(r, (&b""[..],   Ok(())));
        let r = skip_many(0, || token(b'a')).parse(&b"a"[..]   ); assert_eq!(r, (&b"a"[..],   Ok(())));
        let r = skip_many(1, || token(b'a')).parse(&b""[..]    ); assert_eq!(r, (&b""[..],   Err(Error::expected(b'a'))));
        let r = skip_many(1, || token(b'a')).parse(&b"a"[..]   ); assert_eq!(r, (&b""[..],   Ok(())));
        let r = skip_many(2, || token(b'a')).parse(&b""[..]    ); assert_eq!(r, (&b""[..],   Err(Error::expected(b'a'))));
        let r = skip_many(2, || token(b'a')).parse(&b"a"[..]   ); assert_eq!(r, (&b""[..],   Err(Error::expected(b'a'))));
        let r = skip_many(2, || token(b'a')).parse(&b"aa"[..]  ); assert_eq!(r, (&b""[..],   Ok(())));
        let r = skip_many(2, || token(b'a')).parse(&b"aaa"[..] ); assert_eq!(r, (&b"a"[..],  Ok(())));
        let r = skip_many(2, || token(b'a')).parse(&b"aaab"[..]); assert_eq!(r, (&b"ab"[..], Ok(())));
        let r = skip_many(2, || token(b'a')).parse(&b"aab"[..] ); assert_eq!(r, (&b"b"[..],  Ok(())));
        let r = skip_many(2, || token(b'a')).parse(&b"ab"[..]  ); assert_eq!(r, (&b"b"[..],  Err(Error::expected(b'a'))));
        let r = skip_many(2, || token(b'a')).parse(&b"b"[..]   ); assert_eq!(r, (&b"b"[..],  Err(Error::expected(b'a'))));
    }

    #[test]
    #[should_panic]
    fn panic_many_range_lt() {
        let r = many(2..1, || token(b'a'));
        assert_eq!(r.parse(&b"aaaab"[..]), (&b"ab"[..], Ok(vec![b'a', b'a', b'a'])));
    }

    #[test]
    #[should_panic]
    fn panic_skip_many_range_lt() {
        assert_eq!(skip_many(2..1, || token(b'a')).parse(&b"aaaab"[..]), (&b"ab"[..], Ok(())));
    }

    #[test]
    #[should_panic]
    fn panic_many_till_range_lt() {
        let r: (_, Result<Vec<_>, _>) = many_till(2..1, || token(b'a'), || token(b'b')).parse(&b"aaaab"[..]); assert_eq!(r, (&b"ab"[..], Ok(vec![b'a', b'a', b'a'])));
    }
}
