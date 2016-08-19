//! Types which facillitates the chaining of parsers and their results.

pub mod numbering;
#[cfg(feature = "tendril")]
pub mod tendril;

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
    fn to_vec(&self) -> Vec<Self::Token>;

    /// Consumes self to create an owned vector of tokens.
    ///
    /// Will allocate if the implementation borrows storage or does not use an owned type
    /// compatible with `Vec` internally.
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

    fn to_vec(&self) -> Vec<Self::Token> {
        (&self[..]).to_vec()
    }

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

    fn to_vec(&self) -> Vec<Self::Token> {
        (&self[..]).chars().collect()
    }

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

    // Primitive methods

    /// Peeks at the next token in the input without consuming it. `None` if no more input is
    /// available.
    ///
    /// Note: Is allowed to refill automatically or any other appropriate action if the input does
    /// not contain any more data.
    #[inline]
    fn peek(&mut self) -> Option<Self::Token>;

    /// Pops a token off the start of the input. `None` if no more input is available.
    ///
    /// Note: Is allowed to refill automatically or any other appropriate action if the input does
    /// not contain any more data.
    #[inline]
    fn pop(&mut self) -> Option<Self::Token>;

    /// Attempt to consume `n` tokens, if it fails do not advance the position but return `None`.
    ///
    /// Note: Is allowed to refill automatically or any other appropriate action if the input does
    /// not contain any more data.
    #[inline]
    fn consume(&mut self, n: usize) -> Option<Self::Buffer>;

    /// Runs the closure `F` on the tokens *in order* until it returns false, all tokens up to that
    /// token will be returned as a buffer and discarded from the current input. MUST never run the
    /// closure more than once on the exact same token.
    ///
    /// If the end of the input is reached, the whole input is returned.
    ///
    /// Note: Is allowed to refill automatically or any other appropriate action if the input does
    /// not contain any more data.
    #[inline]
    fn consume_while<F>(&mut self, f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool;

    /// Returns the buffer from the marker to the current position, discarding the
    /// backtracking position carried by the marker.
    #[inline]
    fn consume_from(&mut self, m: Self::Marker) -> Self::Buffer;

    /// Returns the remainder of the input in a buffer.
    ///
    /// Note: Will refill the intenal buffer until no more data is available if the underlying
    /// implementation supports it.
    #[inline]
    fn consume_remaining(&mut self) -> Self::Buffer;

    /// Runs the closure `F` on the tokens *in order* until it returns false, all tokens up to that
    /// token will be discarded from the current input.
    ///
    /// MUST never run the closure more than once on the exact same token.
    ///
    /// If the end of the input is reached, the whole input is discarded.
    ///
    /// Note: Default implementation uses `consume_while` and makes the assumption that it will
    /// optimize away the resulting `Self::Buffer`.
    #[inline]
    fn skip_while<F>(&mut self, f: F)
      where F: FnMut(Self::Token) -> bool {
        self.consume_while(f);
    }

    /// Marks the current position to be able to backtrack to it using `restore`.
    #[inline]
    fn mark(&self) -> Self::Marker;

    /// Resumes from a previously marked state.
    #[inline(always)]
    fn restore(self, m: Self::Marker) -> Self;
}

impl<'a, I: Copy + PartialEq> Input for &'a [I] {
    type Token  = I;
    type Marker = &'a [I];
    type Buffer = &'a [I];

    #[inline]
    fn peek(&mut self) -> Option<Self::Token> {
        self.first().cloned()
    }

    #[inline]
    fn pop(&mut self) -> Option<Self::Token> {
        self.first().cloned().map(|c| {
            *self = &self[1..];

            c
        })
    }

    #[inline]
    fn consume(&mut self, n: usize) -> Option<Self::Buffer> {
        if n > self.len() {
            None
        } else {
            let b = &self[..n];

            *self = &self[n..];

            Some(b)
        }
    }

    #[inline]
    fn consume_while<F>(&mut self, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        if let Some(n) = self.iter().position(|c| !f(*c)) {
            let b = &self[..n];

            *self = &self[n..];

            b
        }  else {
            let b = &self[..];

            *self = &self[..0];

            b
        }
    }

    #[inline]
    fn consume_from(&mut self, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.len()]
    }

    #[inline]
    fn consume_remaining(&mut self) -> Self::Buffer {
        let b = &self[..];

        *self = &self[..0];

        b
    }

    #[inline]
    fn mark(&self) -> Self::Marker {
        self
    }

    #[inline]
    fn restore(self, m: Self::Marker) -> Self {
        m
    }
}

impl<'a> Input for &'a str {
    type Token  = char;
    type Marker = &'a str;
    type Buffer = &'a str;

    #[inline]
    fn peek(&mut self) -> Option<Self::Token> {
        self.chars().next()
    }

    #[inline]
    fn pop(&mut self) -> Option<Self::Token> {
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
    fn consume(&mut self, n: usize) -> Option<Self::Buffer> {
        match self.char_indices().enumerate().take(n + 1).last() {
            // num always equal to n if self contains more than n characters
            Some((num, (pos, _))) if n == num => {
                let b = &self[..pos];

                *self = &self[pos..];

                Some(b)
            },
            // num always equal to n - 1 if self contains exactly n characters
            Some((num, _)) if n == num + 1 => {
                let b = &self[..];

                *self = &self[..0];

                Some(b)
            },
            _ => None,
        }
    }

    #[inline]
    fn consume_while<F>(&mut self, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        // We need to find the character following the one which did not match
        if let Some((pos, _)) = self.char_indices().skip_while(|&(_, c)| f(c)).next() {
            let b = &self[..pos];

            *self = &self[pos..];

            b
        } else {
            let b = &self[..];

            *self = &self[..0];

            b
        }
    }

    #[inline]
    fn consume_from(&mut self, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.len()]
    }

    #[inline]
    fn consume_remaining(&mut self) -> Self::Buffer {
        let b = &self[..];

        *self = &self[..0];

        b
    }

    #[inline]
    fn mark(&self) -> Self::Marker {
        self
    }

    #[inline]
    fn restore(self, m: Self::Marker) -> Self {
        m
    }
}

/// A type alias for an `Input` with a token type of `u8`.
pub trait U8Input: Input<Token=u8> {}

impl<T> U8Input for T
  where T: Input<Token=u8> {}

// TODO: More docs
/// A parser.
pub trait Parser<I: Input> {
    /// Output type created by the parser, may refer to data owned by `I`.
    type Output;
    /// Error type created by the parser, may refer to data owned by `I`.
    type Error;

    /// Apply the parser to an input `I`.
    fn parse(self, I) -> (I, Result<Self::Output, Self::Error>);
}

impl<I, T, E, F> Parser<I> for F
  where I: Input,
        F: FnOnce(I) -> (I, Result<T, E>) {
    type Output = T;
    type Error  = E;

    fn parse(self, i: I) -> (I, Result<T, E>) {
        (self)(i)
    }
}

/// Returns `t` as a success value in the parsing context.
///
/// Equivalent to Haskell's `return` function in the `Monad` typeclass.
///
/// # Example
///
/// ```
/// use chomp::types::{Input, parse_only, ret};
///
/// let r = parse_only(|i|
///     // Annotate the error type
///     ret::<_, ()>("Wohoo, success!"),
///     b"some input");
///
/// assert_eq!(r, Ok("Wohoo, success!"));
/// ```
#[inline]
pub fn ret<I: Input, T, E>(t: T) -> impl Parser<I, Output=T, Error=E> {
    move |i| (i, Ok(t))
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
pub fn err<I: Input, T, E>(e: E) -> impl Parser<I, Output=T, Error=E> {
    move |i| (i, Err(e))
}

/// Converts a `Result` into a `Parser`, preserving parser state.
///
/// To convert an `Option` into a `Parser` it is recommended to use
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
pub fn from_result<I: Input, T, E>(r: Result<T, E>) -> impl Parser<I, Output=T, Error=E> {
    move |i| (i, r)
}

/*
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
*/
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
pub fn bind<I, M, F, R>(m: M, f: F) -> impl Parser<I, Output=R::Output, Error=M::Error>
  where I: Input,
        M: Parser<I>,
        F: FnOnce(M::Output) -> R,
        R: Parser<I, Error=M::Error> {
    move |i| match m.parse(i) {
        (i, Ok(t))  => f(t).parse(i),
        (i, Err(e)) => (i, Err(e)),
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
pub fn then<I, M, F, R>(m: M, f: F) -> impl Parser<I, Output=R::Output, Error=M::Error>
  where I: Input,
        M: Parser<I>,
        F: FnOnce() -> R,
        R: Parser<I, Error=M::Error> {
    bind(m, |_| f())
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
pub fn map<I, M, F, R>(m: M, f: F) -> impl Parser<I, Output=R, Error=M::Error>
  where I: Input,
        M: Parser<I>,
        F: FnOnce(M::Output) -> R {
    move |i| match m.parse(i) {
        (i, Ok(t))  => (i, Ok(f(t))),
        (i, Err(e)) => (i, Err(e)),
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
pub fn map_err<I, M, F, E>(m: M, f: F) -> impl Parser<I, Output=M::Output, Error=E>
  where I: Input,
        M: Parser<I>,
        F: FnOnce(M::Error) -> E {
    move |i| match m.parse(i) {
        (i, Ok(t))  => (i, Ok(t)),
        (i, Err(e)) => (i, Err(f(e))),
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
pub fn inspect<I, M, F>(m: M, f: F) -> impl Parser<I, Output=M::Output, Error=M::Error>
  where I: Input,
        M: Parser<I>,
        F: FnOnce(&M::Output) {
    move |i| match m.parse(i) {
        (i, Ok(t))      => {
            f(&t);

            (i, Ok(t))
        },
        (i, Err(e)) => (i, Err(e)),
    }
}

/*
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
*/

#[cfg(test)]
pub mod test {
    use super::{Buffer, Input, Parser, bind, err, ret, from_result, inspect};
    use std::fmt::Debug;

    #[test]
    fn ret_test() {
        assert_eq!(ret::<_, _, ()>(23u32).parse(&b"in1"[..]), (&b"in1"[..], Ok(23u32)));
        assert_eq!(ret::<_, _, &str>(23i32).parse(&b"in2"[..]), (&b"in2"[..], Ok(23i32)));
    }

    #[test]
    fn err_test() {
        assert_eq!(err::<_, (), _>(23u32).parse(&b"in1"[..]), (&b"in1"[..], Err(23u32)));
        assert_eq!(err::<_, &str, _>(23i32).parse(&b"in2"[..]), (&b"in2"[..], Err(23i32)));
    }

    #[test]
    fn from_result_test() {
        let i1: Result<u32, &str> = Ok(23);
        let i2: Result<&str, &str> = Err("foobar");

        assert_eq!(from_result(i1).parse(&b"in1"[..]), (&b"in1"[..], Ok(23u32)));
        assert_eq!(from_result(i1).parse(&b"in2"[..]), (&b"in2"[..], Err("foobar")));
    }

    #[test]
    fn monad_left_identity() {
        fn f<I: Input>(n: u32) -> impl Parser<I, Output=u32, Error=()> {
            ret(n + 1)
        }

        let a = 123;
        // return a >>= f
        let lhs = bind(ret(a), f);
        // f a
        let rhs = f(a);

        assert_eq!(lhs.parse(&b"test"[..]), (&b"test"[..], Ok(124)));
        assert_eq!(rhs.parse(&b"test"[..]), (&b"test"[..], Ok(124)));
    }

    #[test]
    fn monad_right_identity() {
        let m1 = ret::<_, _, ()>(1);
        let m2 = ret::<_, _, ()>(1);

        // m1 >>= ret === m2
        let lhs = bind(m1, ret);
        let rhs = m2;

        assert_eq!(lhs.parse(&b"test"[..]), (&b"test"[..], Ok(1)));
        assert_eq!(rhs.parse(&b"test"[..]), (&b"test"[..], Ok(1)));
    }

    #[test]
    fn monad_associativity() {
         fn f<I: Input>(num: u32) -> impl Parser<I, Output=u64, Error=()> {
            ret((num + 1) as u64)
        }

        fn g<I: Input>(num: u64) -> impl Parser<I, Output=u64, Error=()> {
            ret(num * 2)
        }

        let lhs_m = ret::<_, _, ()>(2);
        let rhs_m = ret::<_, _, ()>(2);

        // (m >>= f) >>= g
        let lhs = bind(bind(lhs_m, f), g);
        // m >>= (\x -> f x >>= g)
        let rhs = bind(rhs_m, |x| bind(f(x), g));

        assert_eq!(lhs.parse(&b"test"[..]), (&b"test"[..], Ok(6)));
        assert_eq!(rhs.parse(&b"test"[..]), (&b"test"[..], Ok(6)));
    }

    /*
    #[test]
    fn parse_result_inspect() {
        let mut n1 = 0;
        let mut n2 = 0;
        let i1     = ret::<_, u32, ()>(23);
        let i2     = ret::<_, u32, ()>(23);

        let r1 = inspect(i1, |d: &u32| {
            assert_eq!(d, &23);

            n1 += 1;
        });
        let r2 = inspect(i2, |d: &u32| {
            assert_eq!(d, &23);

            n2 += 1;
        });

        assert_eq!(r1.parse(&b"test"[..]), (&b"test "[..], Ok(23)));
        assert_eq!(n1, 1);
        assert_eq!(r2.parse(&b"test"[..]), (&b"test "[..], Ok(23)));
        assert_eq!(n2, 1);
    }
    */

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
        fn buffer_eq_slice<B: Buffer + Clone, F: Fn(u8) -> B::Token>(b: B, s: &[u8], f: F)
          where B::Token: Debug, {
            assert_eq!(b.len(), s.len());
            assert_eq!(b.is_empty(), s.is_empty());
            assert_eq!(b.clone().fold(0, |n, c| {
                assert_eq!(c, f(s[n]));

                n + 1
            }), s.iter().count());
            assert_eq!(b.to_vec(), s.iter().cloned().map(f).collect::<Vec<_>>());
        }

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
