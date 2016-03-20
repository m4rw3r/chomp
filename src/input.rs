use parse_result::{ParseResult, State};
use parse_result;

use primitives::Guard;

pub trait U8Input: Input<Token=u8> {}

// TODO: More restrictions? Buffer=&[u8]?
impl<T> U8Input for T
  where T: Input<Token=u8> {}

/*
Behaviour on incomplete:

any:
  error, unexpected eof
satisfy:
  error, unexpected eof
satisfy_with:
  error, unexpected eof
token:
  error, unexpected eof
not_token:
  error, unexpected eof
peek:
  return None
peek_next
  error, unexpected eof
take:
  error, unexpected eof
take_while:
  try refill (success: resume scanning, fail: return remainder)
take_while1:
  try refill (success: resume scanning, fail: return remainder)
take_till:
  try refill (success: resume scanning, fail: error, unexpected eof)
scan:
  try refill (success: resume scanning, fail: error, unexpected eof)
run_scanner:
  try refill (success: resume scanning, fail: error, unexpected eof)
take_remainder:
  try refill, return remainder
string:
  try refill (success: resume scanning, fail: error, unexpected eof)
eof:
  try refill (success: fail, unexpected, fail: success)

option:
  failed incomplete == error
or:
  failed incomplete == error
matched_by:
  failed incomplete == error
look_ahead:
  failed incomplete == error

Range<usize>
  many:
    failed incomplete == error
  skip:
    failed incomplete == error
  many_till:
    failed incomplete == error
RangeFrom
  many:
    failed incomplete == error
  skip:
    failed incomplete == error
  many_till:
    failed incomplete == error
RangeFull
  many:
    failed incomplete == error
  skip:
    failed incomplete == error
  many_till:
    failed incomplete == error
*/

/// Primitive operations on `Input` types.
///
/// All parsers only require a few primitive operations to parse data:
pub mod primitives {
    use {Input, ParseResult};
    use primitives::State;
    use primitives::parse_result::new as new_result;

    /// This is a zero-sized type used by the `Primitives` trait implementation to guarantee that
    /// access to primitive methods on `Input` only happens when the `Primitives` trait has been
    /// imported.
    ///
    /// It cannot be instantiated outside of the `Primitives` trait blanket implementation.
    pub struct Guard(());

    /// **Primitive:** Trait enabling primitive actions on an `Input` type.
    ///
    /// # Primitive
    ///
    /// Only used by fundamental parsers and combinators.
    ///
    // FIXME: Rename
    pub trait Primitives: Input {
        #[inline(always)]
        fn first(&self) -> Option<Self::Token> {
            self._first(Guard(()))
        }

        #[inline(always)]
        fn iter(&self) -> Self::Iter {
            self._iter(Guard(()))
        }

        #[inline(always)]
        fn consume(&mut self, n: usize) -> Self::Buffer {
            self._consume(Guard(()), n)
        }

        // TODO: Change to self -> self?
        #[inline(always)]
        fn discard(self, n: usize) -> Self {
            self._discard(Guard(()), n)
        }

        /// Returns the buffer from the marker `m` to the current position, discarding the
        /// backtracking position carried by `m`.
        #[inline(always)]
        fn consume_from(&mut self, m: Self::Marker) -> Self::Buffer {
            self._consume_from(Guard(()), m)
        }

        #[inline]
        fn min_remaining(&self) -> usize {
            self._min_remaining(Guard(()))
        }

        /// Attempts to populate the input with more data, returning the number of additional
        /// tokens which were added.
        ///
        /// # Primitive
        ///
        /// Only used by fundamental parsers and combinators.
        #[inline(always)]
        fn fill(&mut self) -> usize {
            self._fill(Guard(()))
        }

        /// Marks the current position to be able to backtrack to it using `restore`.
        ///
        /// # Example
        ///
        /// ```
        /// use chomp::{take, Input};
        /// use chomp::primitives::Primitives;
        /// use chomp::primitives::{InputBuffer, IntoInner, State};
        ///
        /// let i = &b"Testing";
        ///
        /// assert_eq!(i.buffer(), b"Testing");
        /// assert_eq!(i.is_end(), true);
        ///
        /// // mark and eat one token
        /// let m = i.mark();
        /// let i = i.consume(1);
        ///
        /// assert_eq!(i.buffer(), b"esting");
        ///
        /// // restore and continue parsing
        /// let j = i.restore(m);
        ///
        /// let r = take(j, 4);
        ///
        /// assert_eq!(r.into_inner(), State::Data(input::new(input::END_OF_INPUT, b""), &b"Test"[..]));
        /// ```
        #[inline(always)]
        fn mark(&self) -> Self::Marker {
            self._mark(Guard(()))
        }

        #[inline(always)]
        fn restore(self, m: Self::Marker) -> Self {
            self._restore(Guard(()), m)
        }
    }

    impl<I: Input> Primitives for I {}
}

// FIXME: Update, do not refer to type or linear type
/// Linear type containing the parser state, this type is threaded though `bind` and is also the
/// initial type passed to a parser.
///
/// Coupled with the `ParseResult` type it forms the parser monad:
///
/// ```ignore
/// Fn*(Input<I>, ...) -> ParseResult<I, T, E>;
/// ```
///
/// where ``Fn*`` is the appropriate closure/function trait, `I` the input token type (usually
/// something like `u8`), `...` additional parameters to the parser, `T` the carried type and `E`
/// the potential error type.
pub trait Input: Sized {
    /// The token type of the input
    // TODO: Maybe remove the copy bound at some point?
    type Token: Copy;
    /// A marker type which is used to backtrack using `_mark` and `_restore`.
    type Marker;

    type Iter: Iterator<Item=Self::Token>;
    type Buffer;

    /// Returns `t` as a success value in the parsing context.
    ///
    /// Equivalent to Haskell's `return` function in the `Monad` typeclass.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::parse_only;
    ///
    /// let r = parse_only(|i|
    ///     // Annotate the error type
    ///     i.ret::<_, ()>("Wohoo, success!"),
    ///     b"some input");
    ///
    /// assert_eq!(r, Ok("Wohoo, success!"));
    /// ```
    #[inline]
    fn ret<T, E>(self, t: T) -> ParseResult<Self, T, E> {
        parse_result::new(State::Data(self, t))
    }

    /// Returns `e` as an error value in the parsing context.
    ///
    /// A more general version of Haskell's `fail` function in the `Monad` typeclass.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::{ParseError, parse_only};
    ///
    /// let r = parse_only(|i|
    ///     // Annotate the value type
    ///     i.err::<(), _>("Something went wrong"),
    ///     b"some input");
    ///
    /// assert_eq!(r, Err(ParseError::Error(b"some input", "Something went wrong")));
    /// ```
    #[inline]
    fn err<T, E>(self, e: E) -> ParseResult<Self, T, E> {
        parse_result::new(State::Error(self, e))
    }

    /// Converts a `Result` into a `ParseResult`, preserving parser state.
    ///
    /// To convert an `Option` into a `ParseResult` it is recommended to use
    /// [`Option::ok_or`](https://doc.rust-lang.org/std/option/enum.Option.html#method.ok_or)
    /// or [`Option::ok_or_else`](https://doc.rust-lang.org/std/option/enum.Option.html#method.ok_or_else)
    /// in combination with this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use chomp::{ParseError, parse_only};
    ///
    /// let r = parse_only(|i| i.from_result::<_, ()>(Ok("foo")), b"test");
    ///
    /// assert_eq!(r, Ok("foo"));
    ///
    /// let r = parse_only(|i| i.from_result::<(), _>(Err("error message")), b"test");
    ///
    /// assert_eq!(r, Err(ParseError::Error(&b"test"[..], "error message")));
    /// ```
    #[inline]
    fn from_result<T, E>(self, r: Result<T, E>) -> ParseResult<Self, T, E> {
        match r {
            Ok(t)  => parse_result::new(State::Data(self, t)),
            Err(e) => parse_result::new(State::Error(self, e)),
        }
    }

    // Primitive methods
    /// **Primitive:** See `Primitives::first` for documentation.
    ///
    /// Returns the first remaining item if there are still data to read.
    #[inline(always)]
    fn _first(&self, g: Guard) -> Option<Self::Token> {
        self._iter(g).next()
    }

    /// **Primitive:** See `Primitives::iter` for documentation.
    ///
    /// Iterator over tokens in the input, does not consume any data.
    #[inline]
    fn _iter(&self, Guard) -> Self::Iter;

    /// **Primitive:** See `Primitives::consume` for documentation.
    ///
    /// Consumes a set amount of input tokens, returning a buffer containing them
    // TODO: Should probably be combined with a ret
    #[inline]
    fn _consume(&mut self, Guard, usize) -> Self::Buffer;

    /// **Primitive:** See `Primitives::discard` for documentation.
    ///
    /// Consumes a set amount of input tokens, discarding them.
    #[inline]
    fn _discard(self, Guard, usize) -> Self;

    /// **Primitive:** See `Primitives::consume_from for documentation.
    ///
    /// Returns the buffer from the marker to the current position, discarding the
    /// backtracking position carried by the marker.
    #[inline]
    fn _consume_from(&mut self, Guard, Self::Marker) -> Self::Buffer;

    /// **Primitive:** See `Primitives::remaining` for documentation.
    ///
    /// Returns the number of tokens remaining in this input (only this part of it, more might
    /// follow if `_is_end` is false).
    #[inline]
    fn _min_remaining(&self, Guard) -> usize;

    /// **Primitive:** See `Primitives::fill` for documentation.
    ///
    /// Attempts to populate the input with more data, returning the number of additional
    /// tokens which were added.
    #[inline(always)]
    fn _fill(&mut self, Guard) -> usize;

    /// **Primitive:** See `Primitives::mark` for documentation.
    ///
    /// Marks a position for backtracking along with relevant state.
    #[inline]
    fn _mark(&self, Guard)                 -> Self::Marker;

    /// **Primitive:** See `Primitives::restore` for documentation.
    ///
    /// Resumes from a previously marked state.
    #[inline]
    fn _restore(self, Guard, Self::Marker) -> Self;
}

impl<'a, I: Copy> Input for &'a [I] {
    type Token  = I;
    type Marker = &'a [I];
    type Iter   = ::std::iter::Cloned<::std::slice::Iter<'a, I>>;
    type Buffer = &'a [I];

    #[inline(always)]
    fn _iter(&self, _g: Guard) -> Self::Iter {
        self.iter().cloned()
    }
    #[inline(always)]
    fn _consume(&mut self, _g: Guard, n: usize) -> Self::Buffer {
        let b = &self[..n];
        *self = &self[n..];
        b
    }
    #[inline(always)]
    fn _discard(self, _g: Guard, n: usize) -> Self {
        &self[n..]
    }
    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.len()]
    }
    #[inline(always)]
    fn _min_remaining(&self, _g: Guard) -> usize {
        self.len()
    }
    #[inline(always)]
    fn _fill(&mut self, _g: Guard) -> usize {
        0
    }
    fn _mark(&self, _g: Guard) -> Self::Marker {
        &self
    }
    fn _restore(self, _g: Guard, m: Self::Marker) -> Self {
        m
    }
}

bitflags!{
    pub flags InputMode: u32 {
        /// Default (empty) input state.
        const DEFAULT      = 0,
        /// If set the current slice of input is the last one.
        const END_OF_INPUT = 1,
        /// If a parser has attempted to read incomplete
        const INCOMPLETE   = 2,
    }
}


/// Input buffer type which contains a flag which tells if we might have more data to read.
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InputBuf<'a, I: 'a>(InputMode, &'a [I]);

/// **Primitive:** Creates a new input from the given state and buffer.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
pub fn new_buf<I>(state: InputMode, buffer: &[I]) -> InputBuf<I> {
    InputBuf(state, buffer)
}

impl<'a, I: 'a> InputBuf<'a, I> {
    pub fn is_incomplete(&self) -> bool {
        self.0.contains(INCOMPLETE)
    }
}

impl<'a, I: Copy> Input for InputBuf<'a, I> {
    type Token  = I;
    // TODO: InputMode? INCOMPLETE must be set no matter what
    type Marker = &'a [I];
    type Iter   = ::std::iter::Cloned<::std::slice::Iter<'a, I>>;
    type Buffer = &'a [I];

    #[inline(always)]
    fn _iter(&self, _g: Guard) -> Self::Iter {
        self.1.iter().cloned()
    }
    #[inline(always)]
    fn _consume(&mut self, _g: Guard, n: usize) -> Self::Buffer {
        let b = &self.1[..n];
        self.1 = &self.1[n..];
        b
    }
    #[inline(always)]
    fn _discard(mut self, _g: Guard, n: usize) -> Self {
        self.1 = &self.1[n..];

        self
    }
    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.1.len()]
    }
    #[inline(always)]
    fn _min_remaining(&self, _g: Guard) -> usize {
        self.1.len()
    }
    #[inline(always)]
    fn _fill(&mut self, _g: Guard) -> usize {
        self.0.insert(INCOMPLETE);

        0
    }
    fn _mark(&self, _g: Guard) -> Self::Marker {
        &self.1
    }
    fn _restore(mut self, _g: Guard, m: Self::Marker) -> Self {
        self.1 = m;

        self
    }
}

// FIXME: Delete
/*
/// **Primitive:** Trait limiting the use of `Clone` for `Input`.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
///
pub trait InputClone {
    /// Creates a clone of the instance.
    ///
    /// # Primitive
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn clone(&self) -> Self;
}

/// **Primitive:** Trait exposing the buffer of `Input`.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
///
pub trait InputBuffer<'a> {
    /// The type of each element of the buffer.
    type Item: 'a;

    /// Reveals the internal buffer containig the remainder of the input.
    ///
    /// # Primitive
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn buffer(&self) -> &'a [Self::Item];

    /// Modifies the inner data without leaving the `Input` context.
    ///
    /// # Primitive
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn replace(self, &'a [Self::Item]) -> Self;

    /// Returns true if this is the last available slice of the input.
    ///
    /// # Primitive
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn is_last_slice(&self) -> bool;
}

/// Trait limiting the use of `Clone` for `Input`.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
///
/// # Motivation
///
/// The `Input` type is supposed to be an approximation of a linear type when observed in the
/// monadic parser context. This means that it should not be possible to duplicate or accidentally
/// throw it away as well as restrict when and where an `Input` can be constructed. Not
/// implementing `Clone` or `Copy` solves the first issue.
///
/// However, cloning an `Input` is necessary for backtracking and also allows for slightly more
/// efficient iteration in combinators. This trait allows us to enable cloning selectively.
impl<'a, I: 'a> InputClone for Input<'a, I> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Input(self.0, self.1)
    }
}

/// Trait exposing the buffer of `Input`.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
///
/// # Motivation
///
/// The `Input` type is supposed to be an approximation of a linear type when observed in the
/// monadic parser context. This means that it should not be possible to duplicate or accidentally
/// throw it away as well as restrict when and where an `Input` can be constructed. Not exposing
/// the constructor (to allow destructuring) as well as using `#[must_use]` solves the second
/// issue.
///
/// But to be able to parse data the contents of the `Input` type must be exposed in at least one
/// point, so that data can be examined, and this trait that makes it possible.
impl<'a, I: 'a> InputBuffer<'a> for Input<'a, I> {
    type Item = I;

    #[inline(always)]
    fn buffer(&self) -> &'a [Self::Item] {
        self.1
    }

    #[inline(always)]
    fn replace(self, b: &'a [Self::Item]) -> Self {
        Input(self.0, b)
    }

    #[inline(always)]
    fn is_last_slice(&self) -> bool {
        self.0.contains(END_OF_INPUT)
    }
}
*/

#[cfg(test)]
mod test {
    use std::fmt::Debug;

    use super::{new_buf, Input, InputBuf, DEFAULT, END_OF_INPUT};
    use parse_result::ParseResult;
    use primitives::{IntoInner, State};

    #[test]
    fn make_ret() {
        let i1: InputBuf<u8> = new_buf(END_OF_INPUT, b"in1");
        let i2: InputBuf<u8> = new_buf(DEFAULT,      b"in2");

        let r1: ParseResult<_, u32, ()> = i1.ret::<_, ()>(23u32);
        let r2: ParseResult<_, i32, ()> = i2.ret::<_, ()>(23i32);

        assert_eq!(r1.into_inner(), State::Data(InputBuf(END_OF_INPUT, b"in1"), 23u32));
        assert_eq!(r2.into_inner(), State::Data(InputBuf(DEFAULT, b"in2"), 23i32));
    }

    #[test]
    fn make_err() {
        let i1: InputBuf<u8> = new_buf(END_OF_INPUT, b"in1");
        let i2: InputBuf<u8> = new_buf(DEFAULT,      b"in2");

        let r1: ParseResult<_, (), u32> = i1.err::<(), _>(23u32);
        let r2: ParseResult<_, (), i32> = i2.err::<(), _>(23i32);

        assert_eq!(r1.into_inner(), State::Error(new_buf(END_OF_INPUT, b"in1"), 23u32));
        assert_eq!(r2.into_inner(), State::Error(new_buf(DEFAULT, b"in2"), 23i32));
    }

    #[test]
    fn primitives_slice() {
        use primitives::Primitives;
        run_primitives_test(&b"abc"[..], true);

        let mut s = &b"abc"[..];
        let m = s.mark();
        s.discard(2);
        assert_eq!(s.consume_from(m), &b"ab"[..]);
        assert_eq!(s, &b"c"[..]);
    }

    #[test]
    fn primitives_input_buf_default() {
        use primitives::Primitives;
        run_primitives_test(new_buf(DEFAULT, b"abc"), false);

        let mut s = new_buf(DEFAULT, b"abc");
        let m = s.mark();
        s.discard(2);
        assert_eq!(s.consume_from(m), &b"ab"[..]);
        assert_eq!(s, new_buf(DEFAULT, b"c"));
    }

    #[test]
    fn primitives_input_buf_end() {
        use primitives::Primitives;
        run_primitives_test(new_buf(END_OF_INPUT, b"abc"), true);

        let mut s = new_buf(END_OF_INPUT, b"abc");
        let m = s.mark();
        s.discard(2);
        assert_eq!(s.consume_from(m), &b"ab"[..]);
        assert_eq!(s, new_buf(END_OF_INPUT, b"c"));
    }

    fn run_primitives_test<B: Debug + for<'a> PartialEq<&'a [u8]>, I: Input<Token=u8, Buffer=B>>(mut s: I, last: bool) {
        use primitives::Primitives;

        assert_eq!(s.is_end(), last);
        assert_eq!(s.min_remaining(), 3);
        let m = s.mark();
        assert_eq!(s.min_remaining(), 3);
        assert_eq!(s.first(), Some(b'a'));
        assert_eq!(s.min_remaining(), 3);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'a', b'b', b'c']);
        assert_eq!(s.min_remaining(), 3);
        assert_eq!(s.consume(2), &b"ab"[..]);
        assert_eq!(s.min_remaining(), 1);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'c']);
        assert_eq!(s.consume(1), &b"c"[..]);
        assert_eq!(s.min_remaining(), 0);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![]);
        assert_eq!(s.is_end(), last);
        let mut s = s.restore(m);
        assert_eq!(s.min_remaining(), 3);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'a', b'b', b'c']);
        s.discard(1);
        assert_eq!(s.first(), Some(b'b'));
        assert_eq!(s.min_remaining(), 2);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'b', b'c']);
    }
}
