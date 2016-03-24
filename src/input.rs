use parse_result::{ParseResult, State};
use parse_result;

use primitives::Guard;

pub trait U8Input: Input<Token=u8> {}

// TODO: More restrictions? Buffer=&[u8]?
impl<T> U8Input for T
  where T: Input<Token=u8> {}

/// Primitive operations on `Input` types.
///
/// All parsers only require a few primitive operations to parse data:
pub mod primitives {
    use Input;

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
    // FIXME: Rename and documentation
    pub trait Primitives: Input {
        #[inline(always)]
        fn peek(&mut self) -> Option<Self::Token> {
            self._peek(Guard(()))
        }

        #[inline(always)]
        fn pop(&mut self) -> Option<Self::Token> {
            self._pop(Guard(()))
        }

        #[inline]
        fn consume(&mut self, n: usize) -> Option<Self::Buffer> {
            self._consume(Guard(()), n)
        }

        #[inline]
        fn consume_while<F>(&mut self, f: F) -> Self::Buffer
          where F: FnMut(Self::Token) -> bool {
            self._consume_while(Guard(()), f)
        }

        /// Returns the buffer from the marker `m` to the current position, discarding the
        /// backtracking position carried by `m`.
        #[inline(always)]
        fn consume_from(&mut self, m: Self::Marker) -> Self::Buffer {
            self._consume_from(Guard(()), m)
        }

        #[inline(always)]
        fn consume_remaining(&mut self) -> Self::Buffer {
            self._consume_remaining(Guard(()))
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

// FIXME: Docs
// TODO: More methods?
pub trait Buffer {
    fn len(&self) -> usize;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
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
    type Token: Copy + PartialEq;
    /// A marker type which is used to backtrack using `_mark` and `_restore`.
    type Marker;

    /// An iterator over the loaded data in the input.
    type Iter: Iterator<Item=Self::Token>;
    // TODO: Bounds for common usage (eg. to iterator?)
    type Buffer: Buffer;

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

    /// **Primitive:** See `Primitives::peek` for documentation.
    ///
    /// Peeks at the next token in the input without consuming it. `None` if no more input is
    /// available.
    ///
    /// Note: Will refill automatically.
    #[inline]
    fn _peek(&mut self, Guard) -> Option<Self::Token>;

    /// **Primitive:** See `Primitives::pop` for documentation.
    ///
    /// Pops a token off the start of the input. `None` if no more input is available.
    ///
    /// Note: Will refill automatically.
    #[inline]
    fn _pop(&mut self, Guard) -> Option<Self::Token>;

    /// **Primitive:** See `Primitives::consume` for documentation.
    ///
    /// Attempt to consume `n` tokens, if it fails do not advance the position but return `None`.
    #[inline]
    fn _consume(&mut self, Guard, usize) -> Option<Self::Buffer>;

    /// **Primitive:** See `Primitives::consume_while` for documentation.
    ///
    /// Runs the closure `F` on the tokens in order until it returns false, all tokens up to that
    /// token will be returned as a buffer and discarded from the current input.
    ///
    /// Note: Will refill automatically.
    #[inline]
    fn _consume_while<F>(&mut self, Guard, F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool;

    /// **Primitive:** See `Primitives::consume_from for documentation.
    ///
    /// Returns the buffer from the marker to the current position, discarding the
    /// backtracking position carried by the marker.
    #[inline]
    fn _consume_from(&mut self, Guard, Self::Marker) -> Self::Buffer;

    /// **Primitive:** See `Primitives::consume_remaining` for documentation.
    ///
    /// Returns the remainder of the input in a buffer.
    ///
    /// Note: Will refill the intenal buffer until no more data is available if the underlying
    /// implementation supports it.
    fn _consume_remaining(&mut self, Guard) -> Self::Buffer;

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

impl<'a, I> Buffer for &'a [I] {
    fn len(&self) -> usize {
        (&self[..]).len()
    }
}

impl<'a, I: Copy + PartialEq> Input for &'a [I] {
    type Token  = I;
    type Marker = &'a [I];
    type Iter   = ::std::iter::Cloned<::std::slice::Iter<'a, I>>;
    type Buffer = &'a [I];

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        self.first().cloned()
    }
    #[inline]
    fn _pop(&mut self, _g: Guard) -> Option<Self::Token> {
        self.first().cloned().map(|c| {
            *self = &self[1..];

            c
        })
    }
    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        if n > self.len() {
            None
        } else {
            let b = &self[..n];

            *self = &self[n..];

            Some(b)
        }
    }
    #[inline]
    fn _consume_while<F>(&mut self, _g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        match self.iter().position(|c| !f(*c)) {
            Some(n) => {
                let b = &self[..n];

                *self = &self[n..];

                b
            },
            None => {
                let b = &self[..];

                *self = &self[..0];

                b
            }
        }
    }
    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.len()]
    }
    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        let b = &self[..];

        *self = &self[..0];

        b
    }
    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        &self
    }
    #[inline]
    fn _restore(self, _g: Guard, m: Self::Marker) -> Self {
        m
    }
}

bitflags!{
    pub flags InputMode: u32 {
        /// Default (empty) input state.
        const DEFAULT      = 0,
        /// If a parser has attempted to read incomplete
        const INCOMPLETE   = 1,
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

    pub fn len(&self) -> usize {
        self.1.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, I: Copy + PartialEq> Input for InputBuf<'a, I> {
    type Token  = I;
    // TODO: InputMode? INCOMPLETE must be set no matter what
    type Marker = &'a [I];
    type Iter   = ::std::iter::Cloned<::std::slice::Iter<'a, I>>;
    type Buffer = &'a [I];

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        match self.1.first() {
            Some(c) => Some(*c),
            None    => {
                self.0.insert(INCOMPLETE);

                None
            },
        }
    }
    #[inline]
    fn _pop(&mut self, g: Guard) -> Option<Self::Token> {
        self._peek(g).map(|c| {
            self.1 = &self.1[1..];

            c
        })
    }
    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        if n > self.1.len() {
            self.0.insert(INCOMPLETE);

            None
        } else {
            let b = &self.1[..n];

            self.1 = &self.1[n..];

            Some(b)
        }
    }
    #[inline]
    fn _consume_while<F>(&mut self, _g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        match self.1.iter().position(|c| !f(*c)) {
            Some(n) => {
                let b = &self.1[..n];

                self.1 = &self.1[n..];

                b
            },
            None => {
                self.0.insert(INCOMPLETE);

                let b = self.1;

                self.1 = &self.1[..0];

                b
            }
        }
    }
    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.1.len()]
    }
    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        let b = self.1;

        self.1 = &self.1[..0];

        b
    }
    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        &self.1
    }
    #[inline]
    fn _restore(mut self, _g: Guard, m: Self::Marker) -> Self {
        self.1 = m;

        self
    }
}

impl<'a> Buffer for &'a str {
    fn len(&self) -> usize {
        (&self[..]).len()
    }
}

impl<'a> Input for &'a str {
    type Token  = char;
    type Marker = &'a str;
    type Iter   = ::std::str::Chars<'a>;
    type Buffer = &'a str;

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        self.chars().next()
    }
    #[inline]
    fn _pop(&mut self, _g: Guard) -> Option<Self::Token> {
        let mut iter = self.char_indices();

        iter.next().map(|(_, c)| {
            match iter.next().map(|(p, _)| p) {
                Some(n) => *self = &self[n..],
                None    => *self = &self[..0],
            }

            c
        })
    }
    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        match self.char_indices().enumerate().take(n + 1).last() {
            // n always less than num if self contains more than n characters
            Some((num, (pos, _))) if n < num => {
                let b = &self[..pos];

                *self = &self[pos..];

                Some(b)
            },
            _ => None,
        }
    }
    #[inline]
    fn _consume_while<F>(&mut self, _g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        // We need to find the character following the one which did not match
        match self.char_indices().skip_while(|&(_, c)| f(c)).next() {
            Some((pos, _)) => {
                let b = &self[..pos];

                *self = &self[pos..];

                b
            },
            None => {
                let b = &self[..];

                *self = &self[..0];

                b
            }
        }
    }
    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.len()]
    }
    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        let b = &self[..];

        *self = &self[..0];

        b
    }
    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        &self
    }
    #[inline]
    fn _restore(self, _g: Guard, m: Self::Marker) -> Self {
        m
    }
}

/*
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

    /*
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
        let mut s = s.restore(m);
        assert_eq!(s.min_remaining(), 3);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'a', b'b', b'c']);
        s.discard(1);
        assert_eq!(s.first(), Some(b'b'));
        assert_eq!(s.min_remaining(), 2);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![b'b', b'c']);
    }
    */
}*/
