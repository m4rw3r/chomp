//! Types which facillitates the chaining of parsers and their results.

pub mod numbering;
#[cfg(feature = "tendril")]
pub mod tendril;

use primitives::{Guard, IntoInner};

/// The buffers yielded parsers consuming a sequence of the input.
///
/// This could either be an owned type or a slice reference depending on the `Input`
/// implementation.
pub trait Buffer: PartialEq<Self> {
    /// The token type of this buffer.
    type Token: Copy + PartialEq;

    /// Applies a function in order on all tokens present in the buffer carrying an accumulator
    /// value `B` between invocations. The buffer is consumed as part of the folding and the last
    /// value of the accumulator is returned.
    // Would be prefereable if there was a &self -> Iterator method, but that does not work for
    // owned or maybe owned since the lifetimes will be wrong for one or the other. Higher Ranked
    // Trait Bounds (HRTB) does not seem to work either since it is not possible to later
    // instantiate the type in a function signature with a concrete lifetime without running into
    // an "expected bound lifetime but found concrete lifetime" error. Instantiation for HRTBs seem
    // to only take place in the actual code, not when a type is used in eg. a where clause.
    fn fold<B, F>(self, B, F) -> B
      where F: FnMut(B, Self::Token) -> B;

    /// Runs the supplied function on a borrow of each token present in the buffer. Invoked in
    /// order and once per token.
    // Same reason for above for not returning an iterator.
    fn iterate<F>(&self, F)
      where F: FnMut(Self::Token);

    /// The number of tokens present in this buffer.
    fn len(&self) -> usize;

    /// Copies all the tokens in this buffer to a new `Vec`.
    #[cfg(feature="std")]
    fn to_vec(&self) -> Vec<Self::Token>;

    /// Consumes self to create an owned vector of tokens.
    ///
    /// Will allocate if the implementation borrows storage or does not use an owned type
    /// compatible with `Vec` internally.
    #[cfg(feature="std")]
    fn into_vec(self) -> Vec<Self::Token>;

    /// Returns true if this buffer is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, I: Copy + PartialEq> Buffer for &'a [I] {
    type Token = I;

    fn fold<B, F>(self, init: B, f: F) -> B
      where F: FnMut(B, Self::Token) -> B {
        (&self[..]).iter().cloned().fold(init, f)
    }

    fn iterate<F>(&self, mut f: F)
      where F: FnMut(Self::Token) {
        for c in (&self[..]).iter().cloned() {
            f(c)
        }
    }

    fn len(&self) -> usize {
        // Slice to reach inherent method to prevent infinite recursion
        (&self[..]).len()
    }

    #[cfg(feature="std")]
    fn to_vec(&self) -> Vec<Self::Token> {
        (&self[..]).to_vec()
    }

    #[cfg(feature="std")]
    fn into_vec(self) -> Vec<Self::Token> {
        (&self[..]).to_vec()
    }
}

impl<'a> Buffer for &'a str {
    type Token = char;

    fn fold<B, F>(self, init: B, f: F) -> B
      where F: FnMut(B, Self::Token) -> B {
        self.chars().fold(init, f)
    }

    fn iterate<F>(&self, mut f: F)
      where F: FnMut(Self::Token) {
        for c in self.chars() {
            f(c)
        }
    }

    fn len(&self) -> usize {
        self.chars().count()
    }

    fn is_empty(&self) -> bool {
        (&self[..]).is_empty()
    }

    #[cfg(feature="std")]
    fn to_vec(&self) -> Vec<Self::Token> {
        (&self[..]).chars().collect()
    }

    #[cfg(feature="std")]
    fn into_vec(self) -> Vec<Self::Token> {
        (&self[..]).chars().collect()
    }
}

/// Linear type containing the parser state, this type is threaded though `bind` and is also the
/// initial type passed to a parser.
///
/// Coupled with the `ParseResult` type it forms the parser monad:
///
/// ```ignore
/// Fn*<I: Input>(I, ...) -> ParseResult<I, T, E>;
/// ```
///
/// where ``Fn*`` is the appropriate closure/function trait, `I` the input type (can be something
/// like `[u8]`), `...` additional parameters to the parser, `T` the carried success type and `E`
/// the potential error type.
pub trait Input: Sized {
    /// The token type of the input.
    type Token: Copy + PartialEq;

    /// A marker type which is used to backtrack using `_mark` and `_restore`.
    ///
    /// It should also be possible to use this type to consume the data from the marked position to
    /// the current position.
    #[doc(hidden)]
    type Marker;

    /// The buffer type yielded by this input when multiple tokens are consumed in sequence.
    ///
    /// Can eg. provide zero-copy parsing if the input type is built to support it.
    type Buffer: Buffer<Token=Self::Token>;

    /// Returns `t` as a success value in the parsing context.
    ///
    /// Equivalent to Haskell's `return` function in the `Monad` typeclass.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{Input, parse_only};
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
        ParseResult(self, Ok(t))
    }

    /// Returns `e` as an error value in the parsing context.
    ///
    /// A more general version of Haskell's `fail` function in the `Monad` typeclass.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{Input, parse_only};
    ///
    /// let r = parse_only(|i|
    ///     // Annotate the value type
    ///     i.err::<(), _>("Something went wrong"),
    ///     b"some input");
    ///
    /// assert_eq!(r, Err((&b"some input"[..], "Something went wrong")));
    /// ```
    #[inline]
    fn err<T, E>(self, e: E) -> ParseResult<Self, T, E> {
        ParseResult(self, Err(e))
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
    /// use chomp::prelude::{Input, parse_only};
    ///
    /// let r = parse_only(|i| i.from_result::<_, ()>(Ok("foo")), b"test");
    ///
    /// assert_eq!(r, Ok("foo"));
    ///
    /// let r = parse_only(|i| i.from_result::<(), _>(Err("error message")), b"test");
    ///
    /// assert_eq!(r, Err((&b"test"[..], "error message")));
    /// ```
    #[inline]
    fn from_result<T, E>(self, r: Result<T, E>) -> ParseResult<Self, T, E> {
        ParseResult(self, r)
    }

    // Primitive methods

    /// **Primitive:** See `Primitives::peek` for documentation.
    #[inline]
    #[doc(hidden)]
    fn _peek(&mut self, Guard) -> Option<Self::Token>;

    /// **Primitive:** See `Primitives::pop` for documentation.
    #[inline]
    #[doc(hidden)]
    fn _pop(&mut self, Guard) -> Option<Self::Token>;

    /// **Primitive:** See `Primitives::consume` for documentation.
    #[inline]
    #[doc(hidden)]
    fn _consume(&mut self, Guard, usize) -> Option<Self::Buffer>;

    /// **Primitive:** See `Primitives::consume_while` for documentation.
    #[inline]
    #[doc(hidden)]
    fn _consume_while<F>(&mut self, Guard, F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool;

    /// **Primitive:** See `Primitives::consume_from for documentation.
    #[inline]
    #[doc(hidden)]
    fn _consume_from(&mut self, Guard, Self::Marker) -> Self::Buffer;

    /// **Primitive:** See `Primitives::consume_remaining` for documentation.
    #[inline]
    #[doc(hidden)]
    fn _consume_remaining(&mut self, Guard) -> Self::Buffer;

    /// **Primitive:** See `Primitives::skip_while` for documentation.
    #[inline]
    #[doc(hidden)]
    fn _skip_while<F>(&mut self, g: Guard, f: F)
      where F: FnMut(Self::Token) -> bool {
        self._consume_while(g, f);
    }

    /// **Primitive:** See `Primitives::mark` for documentation.
    #[inline]
    #[doc(hidden)]
    fn _mark(&self, Guard) -> Self::Marker;

    /// **Primitive:** See `Primitives::restore` for documentation.
    #[inline]
    #[doc(hidden)]
    fn _restore(self, Guard, Self::Marker) -> Self;
}

impl<'a, I: Copy + PartialEq> Input for &'a [I] {
    type Token  = I;
    type Marker = &'a [I];
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
    fn _consume_while<F>(&mut self, g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        if let Some(n) = self.iter().position(|c| !f(*c)) {
            let b = &self[..n];

            *self = &self[n..];

            b
        }  else {
            self._consume_remaining(g)
        }
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.len()]
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        let b = &self[..];

        *self = &self[b.len()..];

        b
    }

    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        self
    }

    #[inline]
    fn _restore(self, _g: Guard, m: Self::Marker) -> Self {
        m
    }
}

impl<'a> Input for &'a str {
    type Token  = char;
    type Marker = &'a str;
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
                None    => *self = &self[self.len()..],
            }

            c
        })
    }

    #[inline]
    fn _consume(&mut self, g: Guard, n: usize) -> Option<Self::Buffer> {
        match self.char_indices().enumerate().take(n + 1).last() {
            // num always equal to n if self contains more than n characters
            Some((num, (pos, _))) if n == num => {
                let b = &self[..pos];

                *self = &self[pos..];

                Some(b)
            },
            // num always equal to n - 1 if self contains exactly n characters
            Some((num, _)) if n == num + 1 => {
                Some(self._consume_remaining(g))
            },
            _ => None,
        }
    }

    #[inline]
    fn _consume_while<F>(&mut self, g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        // We need to find the character following the one which did not match
        if let Some((pos, _)) = self.char_indices().skip_while(|&(_, c)| f(c)).next() {
            let b = &self[..pos];

            *self = &self[pos..];

            b
        } else {
            self._consume_remaining(g)
        }
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.len()]
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        let b = &self[..];

        *self = &self[b.len()..];

        b
    }

    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        self
    }

    #[inline]
    fn _restore(self, _g: Guard, m: Self::Marker) -> Self {
        m
    }
}

/// A type alias for an `Input` with a token type of `u8`.
pub trait U8Input: Input<Token=u8> {}

impl<T> U8Input for T
  where T: Input<Token=u8> {}

/// The basic return type of a parser.
///
/// This type satisfies a variant of the `Monad` typeclass. Due to the limitations of Rust's
/// return types closures cannot be returned without boxing which has an unacceptable performance
/// impact.
///
/// To get around this issue and still provide a simple to use and safe (as in hard to accidentally
/// violate the monad laws or the assumptions taken by the parser type) an `Input` wrapper is
/// provided which ensures that the parser state is carried properly through every call to `bind`.
/// This is also known as a Linear Type (emulated through hiding destructors and using the
/// annotation `#[must_use]`).
///
/// Do-notation is provided by the macro `parse!`.
///
/// # Equivalence with Haskell's `Monad` typeclass:
///
/// ```text
/// f >>= g   ≡  f(m).bind(g)
/// f >> g    ≡  f(m).then(g)
/// return a  ≡  m.ret(a)
/// fail a    ≡  m.err(a)
/// ```
///
/// It also satisfies the monad laws:
///
/// ```text
/// return a >>= f   ≡  f a
/// m >>= return     ≡  m
/// (m >>= f) >>= g  ≡  m >>= (\x -> f x >>= g)
/// ```
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ParseResult<I: Input, T, E>(I, Result<T, E>);

impl<I: Input, T, E> ParseResult<I, T, E> {
    /// Sequentially composes the result with a parse action `f`, passing any produced value as
    /// the second parameter.
    ///
    /// The first parameter to the supplied function `f` is the parser state (`Input`). This
    /// state is then passed on to other parsers or used to return a value or an error.
    ///
    /// # Automatic conversion of `E`
    ///
    /// The error value `E` will automatically be converted using the `From` trait to the
    /// desired type. The downside with this using the current stable version of Rust (1.4) is that
    /// the type inferrence will currently not use the default value for the generic `V` and will
    /// therefore require extra type hint for the error.
    ///
    /// # Examples
    ///
    /// ```
    /// use chomp::prelude::{Input, parse_only};
    ///
    /// let r = parse_only(|i| {
    ///         i.ret("data".to_owned())
    ///         // Explicitly state the error type
    ///          .bind::<_, _, ()>(|i, x| i.ret(x + " here!"))
    ///     },
    ///     b"test");
    ///
    /// assert_eq!(r, Ok("data here!".to_owned()));
    /// ```
    ///
    /// Wrapping the expression in a function will both make it easier to compose and also provides
    /// the type-hint for the error in the function signature:
    ///
    /// ```
    /// use chomp::prelude::{Input, ParseResult, parse_only};
    ///
    /// fn parser<I: Input>(i: I, n: i32) -> ParseResult<I, i32, ()> {
    ///     i.ret(n + 10)
    /// }
    ///
    /// let r = parse_only(|i| i.ret(23).bind(parser), b"test");
    ///
    /// assert_eq!(r, Ok(33));
    /// ```
    #[inline]
    pub fn bind<F, U, V>(self, f: F) -> ParseResult<I, U, V>
      where F: FnOnce(I, T) -> ParseResult<I, U, V>,
            V: From<E> {
        match self.1 {
            Ok(t)  => f(self.0, t).map_err(From::from),
            Err(e) => ParseResult(self.0, Err(From::from(e))),
        }
    }

    /// Sequentially composes the result with a parse action `f`, discarding any produced value.
    ///
    /// The first parameter to the supplied function `f` is the parser state (`Input`). This
    /// state is then passed on to other parsers or used to return a value or an error.
    ///
    /// # Relation to `bind`
    ///
    /// ```text
    /// ParseResult::then(g)  ≡  ParseResult::bind(|i, _| g(i))
    /// ```
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{Input, SimpleResult, parse_only};
    ///
    /// fn g<I: Input>(i: I) -> SimpleResult<I, &'static str> {
    ///     i.ret("testing!")
    /// }
    ///
    /// let r1 = parse_only(|i| i.ret("initial state").bind(|i, _| g(i)), b"data");
    /// let r2 = parse_only(|i| i.ret("initial state").then(g), b"data");
    ///
    /// assert_eq!(r1, Ok("testing!"));
    /// assert_eq!(r2, Ok("testing!"));
    /// ```
    #[inline]
    pub fn then<F, U, V>(self, f: F) -> ParseResult<I, U, V>
      where F: FnOnce(I) -> ParseResult<I, U, V>,
            V: From<E> {
        self.bind(|i, _| f(i))
    }

    /// Applies the function `f` on the contained data if the parser is in a success state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{parse_only, any};
    ///
    /// let r = parse_only(|i| any(i).map(|c| c + 12), b"abc");
    ///
    /// assert_eq!(r, Ok(b'm'));
    /// ```
    #[inline]
    pub fn map<U, F>(self, f: F) -> ParseResult<I, U, E>
      where F: FnOnce(T) -> U {
        match self {
            ParseResult(i, Ok(t))  => ParseResult(i, Ok(f(t))),
            ParseResult(i, Err(e)) => ParseResult(i, Err(e)),
        }
    }

    /// Applies the function `f` on the contained error if the parser is in an error state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{Input, parse_only};
    ///
    /// let r = parse_only(|i| i.err::<(), _>("this is")
    ///          .map_err(|e| e.to_owned() + " an error"),
    ///          b"foo");
    ///
    /// assert_eq!(r, Err((&b"foo"[..], "this is an error".to_owned())));
    /// ```
    #[inline]
    pub fn map_err<V, F>(self, f: F) -> ParseResult<I, T, V>
      where F: FnOnce(E) -> V {
        match self {
            ParseResult(i, Ok(t))  => ParseResult(i, Ok(t)),
            ParseResult(i, Err(e)) => ParseResult(i, Err(f(e))),
        }
    }

    /// Calls the function `f` with a reference of the contained data if the parser is in a success
    /// state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{parse_only, take_while};
    ///
    /// let r = parse_only(|i| take_while(i, |c| c != b' ').inspect(|b| {
    ///     println!("{:?}", b); // Prints "test"
    /// }), b"test and more");
    ///
    /// assert_eq!(r, Ok(&b"test"[..]));
    /// ```
    #[inline]
    pub fn inspect<F>(self, f: F) -> ParseResult<I, T, E>
      where F: FnOnce(&T) {
        if let Ok(ref t) = self.1 {
             f(t)
        }

        self
    }
}

/// **Primitive:** Consumes the `ParseResult` and exposes the internal state.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
///
/// # Motivation
///
/// The `ParseResult` type is a semi-linear type, supposed to act like a linear type while used in
/// a parsing context to carry the state. Normally it should be as restrictive as the `Input` type
/// in terms of how much it exposes its internals, but the `IntoInner` trait implementation
/// allows fundamental parsers and combinators to expose the inner `Result` of the `ParseResult`
/// and act on this.
impl<I: Input, T, E> IntoInner for ParseResult<I, T, E> {
    type Inner = (I, Result<T, E>);

    #[inline(always)]
    fn into_inner(self) -> Self::Inner {
        (self.0, self.1)
    }
}

#[cfg(test)]
pub mod test {
    use super::{Buffer, Input, ParseResult};
    use primitives::IntoInner;
    use std::fmt::Debug;

    #[test]
    fn ret() {
        let r1: ParseResult<_, u32, ()>   = b"in1".ret::<_, ()>(23u32);
        let r2: ParseResult<_, i32, &str> = b"in2".ret::<_, &str>(23i32);

        assert_eq!(r1.into_inner(), (&b"in1"[..], Ok(23u32)));
        assert_eq!(r2.into_inner(), (&b"in2"[..], Ok(23i32)));
    }

    #[test]
    fn err() {
        let r1: ParseResult<_, (), u32>   = b"in1".err::<(), _>(23u32);
        let r2: ParseResult<_, &str, i32> = b"in2".err::<&str, _>(23i32);

        assert_eq!(r1.into_inner(), (&b"in1"[..], Err(23u32)));
        assert_eq!(r2.into_inner(), (&b"in2"[..], Err(23i32)));
    }

    #[test]
    fn from_result() {
        let i1: Result<u32, &str> = Ok(23);
        let i2: Result<&str, &str> = Err("foobar");

        let r1 = b"in1".from_result(i1);
        let r2 = b"in2".from_result(i2);

        assert_eq!(r1.into_inner(), (&b"in1"[..], Ok(23u32)));
        assert_eq!(r2.into_inner(), (&b"in2"[..], Err("foobar")));
    }

    #[test]
    fn monad_left_identity() {
        fn f<I: Input>(i: I, n: u32) -> ParseResult<I, u32, ()> {
            i.ret(n + 1)
        }

        let a = 123;
        // return a >>= f
        let lhs = b"test".ret(a).bind(f);
        // f a
        let rhs = f(&b"test"[..], a);

        assert_eq!((lhs.0, lhs.1), (&b"test"[..], Ok(124)));
        assert_eq!((rhs.0, rhs.1), (&b"test"[..], Ok(124)));
    }

    #[test]
    fn monad_right_identity() {
        let m1 = b"test".ret::<_, ()>(1);
        let m2 = b"test".ret::<_, ()>(1);

        // m1 >>= ret === m2
        let lhs = m1.bind::<_, _, ()>(Input::ret);
        let rhs = m2;

        assert_eq!((lhs.0, rhs.1), (&b"test"[..], Ok(1)));
        assert_eq!((rhs.0, lhs.1), (&b"test"[..], Ok(1)));
    }

    #[test]
    fn monad_associativity() {
         fn f<I: Input>(i: I, num: u32) -> ParseResult<I, u64, ()> {
            i.ret((num + 1) as u64)
        }

        fn g<I: Input>(i: I, num: u64) -> ParseResult<I, u64, ()> {
            i.ret(num * 2)
        }

        let lhs_m = b"test".ret::<_, ()>(2);
        let rhs_m = b"test".ret::<_, ()>(2);

        // (m >>= f) >>= g
        let lhs = lhs_m.bind(f).bind(g);
        // m >>= (\x -> f x >>= g)
        let rhs = rhs_m.bind(|i, x| f(i, x).bind(g));

        assert_eq!((lhs.0, lhs.1), (&b"test"[..], Ok(6)));
        assert_eq!((rhs.0, rhs.1), (&b"test"[..], Ok(6)));
    }

    #[test]
    fn parse_result_inspect() {
        use primitives::IntoInner;

        let mut n1 = 0;
        let mut n2 = 0;
        let i1     = b"test ".ret::<u32, ()>(23);
        let i2     = b"test ".ret::<u32, ()>(23);

        let r1 = i1.inspect(|d: &u32| {
            assert_eq!(d, &23);

            n1 += 1;
        });
        let r2 = i2.inspect(|d: &u32| {
            assert_eq!(d, &23);

            n2 += 1;
        });

        assert_eq!(r1.into_inner(), (&b"test "[..], Ok(23)));
        assert_eq!(n1, 1);
        assert_eq!(r2.into_inner(), (&b"test "[..], Ok(23)));
        assert_eq!(n2, 1);
    }

    #[test]
    fn input_propagation() {
        let mut n_calls = 0;

        let i = b"test1".ret::<_, ()>(23);

        assert_eq!(i.0, b"test1");
        assert_eq!(i.1, Ok(23));

        let r: ParseResult<_, _, ()> = i.bind(|i, t| { n_calls += 1; i.ret(t) });

        assert_eq!((r.0, r.1), (&b"test1"[..], Ok(23)));
        assert_eq!(n_calls, 1);
    }

    #[test]
    fn error_propagation() {
        let mut n_calls = 0;

        let i = b"test1".err::<(), _>(23);

        assert_eq!(i.0, b"test1");
        assert_eq!(i.1, Err(23));

        let r = i.bind(|i, t| { n_calls += 1; i.ret(t) });

        assert_eq!((r.0, r.1), (&b"test1"[..], Err(23)));
        assert_eq!(n_calls, 0);
    }

    #[test]
    fn slice() {
        fn f<I: Input>(i: I, n: u32) -> ParseResult<I, u32, ()> { i.ret(n + 1) }

        let lhs = (&b"test"[..]).ret(123).bind(f);
        let rhs = f(&b"test"[..], 123);

        assert_eq!((lhs.0, lhs.1), (&b"test"[..], Ok(124)));
        assert_eq!((rhs.0, rhs.1), (&b"test"[..], Ok(124)));
    }

    #[test]
    fn test_consuming_whole_slice_does_not_reset_the_pointer() {
        use primitives::Primitives;

        let slice: &[u8] = b"abc";
        let mut b = slice;
        b.consume(1);
        b.consume_while(|_| true);
        let consumed = b.as_ptr() as usize - slice.as_ptr() as usize;
        assert_eq!(consumed, 3);

        let mut b = slice;
        b.consume(3);
        let consumed = b.as_ptr() as usize - slice.as_ptr() as usize;
        assert_eq!(consumed, 3);

        let mut b = slice;
        b.pop();
        b.pop();
        b.pop();
        let consumed = b.as_ptr() as usize - slice.as_ptr() as usize;
        assert_eq!(consumed, 3);
    }

    #[test]
    fn test_consuming_whole_str_does_not_reset_the_pointer() {
        use primitives::Primitives;

        let slice: &str = "abc";
        let mut b = slice;
        b.consume(1);
        b.consume_while(|_| true);
        let consumed = b.as_ptr() as usize - slice.as_ptr() as usize;
        assert_eq!(consumed, 3);

        let mut b = slice;
        b.consume(3);
        let consumed = b.as_ptr() as usize - slice.as_ptr() as usize;
        assert_eq!(consumed, 3);

        let mut b = slice;
        b.pop();
        b.pop();
        b.pop();
        let consumed = b.as_ptr() as usize - slice.as_ptr() as usize;
        assert_eq!(consumed, 3);
    }

    #[test]
    fn test_slice() {
        run_primitives_test(&b"abc"[..], |x| x);
    }

    #[test]
    fn test_string() {
        run_primitives_test(&"abc"[..], |c| c as char);
    }

    /// Should recieve an Input with the tokens 'a', 'b' and 'c' remaining.
    pub fn run_primitives_test<I: Input, F: Fn(u8) -> I::Token>(mut s: I, f: F)
      where I::Token:  Debug,
            I::Buffer: Clone {
        use primitives::Primitives;

        fn buffer_eq_slice<B: Buffer + Clone, F: Fn(u8) -> B::Token>(b: B, s: &[u8], f: F)
          where B::Token: Debug {
            assert_eq!(b.len(), s.len());
            assert_eq!(b.is_empty(), s.is_empty());
            assert_eq!(b.clone().fold(0, |n, c| {
                assert_eq!(c, f(s[n]));

                n + 1
            }), s.iter().count());
            buffer_to_vec(b, s, f);
        }

        #[cfg(feature="std")]
        fn buffer_to_vec<B: Buffer + Clone, F: Fn(u8) -> B::Token>(b: B, s: &[u8], f: F)
          where B::Token: Debug {
            assert_eq!(b.to_vec(), s.iter().cloned().map(f).collect::<Vec<_>>());
        }

        #[cfg(not(feature="std"))]
        fn buffer_to_vec<B: Buffer + Clone, F: Fn(u8) -> B::Token>(_: B, _: &[u8], _: F)
          where B::Token: Debug {}

        let m = s.mark();
        assert_eq!(s.peek(), Some(f(b'a')));
        assert_eq!(s.pop(),  Some(f(b'a')));
        assert_eq!(s.peek(), Some(f(b'b')));
        assert_eq!(s.pop(),  Some(f(b'b')));
        assert_eq!(s.peek(), Some(f(b'c')));
        assert_eq!(s.pop(),  Some(f(b'c')));
        assert_eq!(s.peek(), None);
        assert_eq!(s.pop(),  None);
        assert_eq!(s.peek(), None);
        assert_eq!(s.pop(),  None);
        assert!(s.consume(1).is_none());
        buffer_eq_slice(s.consume_remaining(), &b""[..], &f);

        {
            let mut n = 0;

            let b = s.consume_while(|_| { n += 1; true });

            assert_eq!(n, 0);
            buffer_eq_slice(b, &b""[..], &f);
        }

        let mut s = s.restore(m);
        assert_eq!(s.peek(), Some(f(b'a')));
        let m = s.mark();
        buffer_eq_slice(s.consume_remaining(), &b"abc"[..], &f);
        assert_eq!(s.peek(), None);
        let mut s = s.restore(m);
        assert_eq!(s.peek(), Some(f(b'a')));
        let m = s.mark();

        {
            let b = s.consume(2);

            assert_eq!(b.is_some(), true);
            buffer_eq_slice(b.unwrap(), &b"ab"[..], &f);
        }

        assert_eq!(s.peek(), Some(f(b'c')));

        let mut s = s.restore(m);
        assert_eq!(s.peek(), Some(f(b'a')));
        let m = s.mark();

        {
            let b = s.consume(3);

            assert_eq!(b.is_some(), true);
            buffer_eq_slice(b.unwrap(), &b"abc"[..], &f);
        }

        assert_eq!(s.peek(), None);
        let mut s = s.restore(m);
        let m = s.mark();

        if let Some(b) = s.consume(3) {
            let mut v = Vec::new();

            assert_eq!(b.len(), 3);
            assert_eq!(b.is_empty(), false);

            b.iterate(|c| {
                v.push(c);
            });

            assert_eq!(v, [f(b'a'), f(b'b'), f(b'c')]);
            assert_eq!(b.len(), 3);
            assert_eq!(b.is_empty(), false);
        }
        else {
            panic!("s.consume(3) failed");
        }

        assert_eq!(s.peek(), None);
        let mut s = s.restore(m);
        assert_eq!(s.peek(), Some(f(b'a')));
        let m = s.mark();

        {
            let mut n = 0;

            let b = s.consume_while(|c| {
                assert_eq!(c, f(b"abc"[n]));

                n += 1;

                n < 3
            });

            assert_eq!(n, 3);
            buffer_eq_slice(b, &b"ab"[..], &f);
        }

        assert_eq!(s.peek(), Some(f(b'c')));
        assert_eq!(s.pop(),  Some(f(b'c')));
        assert_eq!(s.peek(), None);
        assert_eq!(s.pop(),  None);

        buffer_eq_slice(s.consume_from(m), &b"abc"[..], &f);
    }
}
