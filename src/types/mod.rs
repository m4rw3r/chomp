//! Types which facillitates the chaining of parsers and their results.

use std::marker::PhantomData;

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
pub trait Input {
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
    /// token will be returned as a buffer and discarded from the current input.
    ///
    /// MUST never run the closure more than once on the exact same token.
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
/// The parser monad type.
///
/// Do-notation is provided by the macro `parse!`.
///
/// # Equivalence with Haskell's `Monad` typeclass:
///
/// ```text
/// f >>= g   ≡  f().bind(g)
/// f >> g    ≡  f().then(g)
/// return a  ≡  ret(a)
/// fail a    ≡  err(a)
/// ```
///
/// It also satisfies the monad laws:
///
/// ```ignore
/// ret(a).bind(f)    =  f(a)
/// m.then(ret)       =  m
/// m.bind(f).bind(g) =  m.bind(|x| f(x).bind(g))
/// ```
pub trait Parser<I: Input> {
    /// Output type created by the parser, may refer to data owned by `I`.
    type Output;
    /// Error type created by the parser, may refer to data owned by `I`.
    type Error;

    /// Apply the parser to an input `I`.
    fn parse(self, I) -> (I, Result<Self::Output, Self::Error>);

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
    /// #![feature(conservative_impl_trait)]
    ///
    /// use chomp::prelude::{Parser, parse_only, ret};
    ///
    /// let r = parse_only(ret("data")
    ///     // Explicitly state the error type
    ///     .bind(|x| ret::<_, ()>(x.to_owned() + " here!")),
    ///     b"test");
    ///
    /// assert_eq!(r, Ok("data here!".to_owned()));
    /// ```
    ///
    /// Wrapping the expression in a function will both make it easier to compose and also provides
    /// the type-hint for the error in the function signature:
    ///
    /// ```
    /// #![feature(conservative_impl_trait)]
    ///
    /// use chomp::prelude::{Input, Parser, parse_only, ret};
    ///
    /// fn parser<I: Input>(n: i32) -> impl Parser<I, Output=i32, Error=()> {
    ///     ret(n + 10)
    /// }
    ///
    /// let r = parse_only(ret(23).bind(parser), b"test");
    ///
    /// assert_eq!(r, Ok(33));
    /// ```
    #[inline(always)]
    // TODO: Add From::from
    // TODO: Is it possible to remove R here?
    // I is required to be a type-parameter to the created parser in case Self does not have
    // anything restricting I, then the parser we are binding to needs to provide that.
    fn bind<F, R>(self, f: F) -> BindParser<I, Self, F, R>
      where F: FnOnce(Self::Output) -> R,
            R: Parser<I, Error=Self::Error>,
            Self: Sized {
        BindParser { p: self, f: f, _i: PhantomData }
    }

    /// Sequentially composes the result with a parse action `f`, discarding any produced value.
    ///
    /// The first parameter to the supplied function `f` is the parser state (`Input`). This
    /// state is then passed on to other parsers or used to return a value or an error.
    ///
    /// # Relation to `bind`
    ///
    /// ```text
    /// p.then(g)  ≡  p.bind(|_| g)
    /// ```
    ///
    /// # Example
    ///
    /// ```
    /// #![feature(conservative_impl_trait)]
    ///
    /// use chomp::prelude::{Input, Parser, parse_only, ret};
    ///
    /// fn g<I: Input>() -> impl Parser<I, Output=&'static str, Error=()> {
    ///     ret("testing!")
    /// }
    ///
    /// let r1 = parse_only(ret("initial state").bind(|_| g()), b"data");
    /// let r2 = parse_only(ret("initial state").then(g()), b"data");
    ///
    /// assert_eq!(r1, Ok("testing!"));
    /// assert_eq!(r2, Ok("testing!"));
    /// ```
    #[inline(always)]
    // TODO: Add From::from
    // TODO: Tests, also with an unbounded I (from eg. ret or err)
    fn then<P>(self, p: P) -> ThenParser<I, Self, P>
      where P: Parser<I, Error=Self::Error>,
            Self: Sized {
        ThenParser { p: self, q: p, _i: PhantomData }
    }

    /// Applies the function `f` on the contained data if the parser is in a success state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{Parser, parse_only, any, ret};
    ///
    /// let r = parse_only(any().map(|c| c + 12), b"abc");
    ///
    /// assert_eq!(r, Ok(b'm'));
    ///
    /// assert_eq!(parse_only(ret::<_, ()>(123).map(|c| c + 12), b"abc"), Ok(135));
    /// ```
    // TODO: Tests
    #[inline(always)]
    fn map<F, R>(self, f: F) -> MapParser<I, Self, F>
      where F: FnOnce(Self::Output) -> R,
            Self: Sized {
        MapParser { p: self, f: f, _i: PhantomData }
    }

    /// Applies the function `f` on the contained error if the parser is in an error state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{Parser, parse_only, err};
    ///
    /// let r = parse_only(err::<(), _>("this is")
    ///          .map_err(|e| e.to_owned() + " an error"), b"foo");
    ///
    /// assert_eq!(r, Err((&b"foo"[..], "this is an error".to_owned())));
    /// ```
    // TODO: Tests
    // TODO: Make sure to use an unbounded I too first in tests
    #[inline(always)]
    fn map_err<F, E>(self, f: F) -> MapErrParser<I, Self, F>
      where F: FnOnce(Self::Error) -> E,
            Self: Sized {
        MapErrParser { p: self, f: f, _i: PhantomData }
    }

    /// Calls the function `f` with a reference of the contained data if the parser is in a success
    /// state.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::prelude::{Parser, parse_only, take_while};
    ///
    /// let r = parse_only(take_while(|c| c != b' ').inspect(|b| {
    ///     println!("{:?}", b); // Prints "test"
    /// }), b"test and more");
    ///
    /// assert_eq!(r, Ok(&b"test"[..]));
    /// ```
    // TODO: Tests
    #[inline(always)]
    fn inspect<F>(self, f: F) -> InspectParser<I, Self, F>
      where F: FnOnce(&Self::Output),
            Self: Sized {
        InspectParser { p: self, f: f, _i: PhantomData }
    }

    /// Tries to match the parser `f`, if `f` fails it tries `g`. Returns the success value of
    /// the first match, otherwise the error of the last one if both fail.
    ///
    /// Incomplete state is propagated from the first one to report incomplete.
    ///
    /// If multiple `or` combinators are used in the same expression, consider using the `parse!` macro
    /// and its alternation operator (`<|>`).
    ///
    /// ```
    /// use chomp::prelude::{Error, Parser, parse_only, token};
    ///
    /// let p = || token(b'a').or(token(b'b'));
    ///
    /// assert_eq!(parse_only(p(), b"abc"), Ok(b'a'));
    /// assert_eq!(parse_only(p(), b"bbc"), Ok(b'b'));
    /// assert_eq!(parse_only(p(), b"cbc"), Err((&b"cbc"[..], Error::expected(b'b'))));
    /// ```
    // TODO: Write the laws for MonadPlus, or should satisfy MonadPlus laws (stronger guarantees
    // compared to Alternative typeclass laws)
    // TODO: Tests
    #[inline(always)]
    fn or<P>(self, p: P) -> OrParser<I, Self, P>
      where P: Parser<I, Output=Self::Output, Error=Self::Error>,
            Self: Sized {
        OrParser { p: self, q: p, _i: PhantomData }
    }

    /// Creates a new parser which matches `Self` and if successful tries to match `P`, if `P` is
    /// also matched the result of `Self` is yielded.
    ///
    /// Equivalent to:
    ///
    /// ```ignore
    /// self.bind(|t| p.map(|_| t))
    /// ```
    // TODO: Get more of the Applicative instance in here, make tests
    // TODO: Docs
    // TODO: Tests, also include test with unbounded existing parser (ret and err) on lhs
    #[inline(always)]
    fn skip<P>(self, p: P) -> SkipParser<I, Self, P>
      where P: Parser<I, Error=Self::Error>,
            Self: Sized {
        // Would be nice to be able to return the following, but conservative impl Trait does not
        // work on traits:
        // self.bind(|t| p.map(|_| t))
        SkipParser{ p: self, q: p, _i: PhantomData }
    }

    /// Turns the parser into a trait object, using the `BoxedParser` type to provide inference and
    /// guarantees that it will satisfy any `P: Parser` generic.
    ///
    /// Useful to unify the types different parsers when eg. returning two different parsers
    /// depending on a condition.
    ///
    /// ```
    /// use chomp::prelude::{Parser, Error, any, token};
    ///
    /// let a = 3;
    ///
    /// let p = if a == 0 {
    ///     any().boxed()
    /// } else {
    ///     token(b'a').boxed()
    /// };
    ///
    /// assert_eq!(p.parse(&b"bcd"[..]), (&b"bcd"[..], Err(Error::expected(b'a'))));
    /// ```
    #[inline(always)]
    fn boxed(self) -> BoxedParser<I, Self::Output, Self::Error>
      where Self: Sized + 'static {
        Box::new(self)
    }
}

/// The type for boxed parsers, created through `Parser::boxed`.
pub type BoxedParser<I, T, E> = Box<BoxParser<I, Output=T, Error=E>>;

/// Trait wrapping a parser to be able to destructure a `Box<BoxParser>` in a sized manner.
/// Recommended to use the `BoxedParser` type-alias instead of `BoxParser` directly.
pub trait BoxParser<I: Input> {
    /// The output type of the boxed parser, analogous to `Parser::Output`.
    type Output;
    /// The error type of the boxed parser, analogous to `Parser::Error`.
    type Error;

    /// Allows destructuring of the box to be able to consume the wrapped contents, analogous to
    /// `Parser::parse`.
    #[inline]
    fn parse_box(self: Box<Self>, i: I) -> (I, Result<Self::Output, Self::Error>);
}

impl<I, P> BoxParser<I> for P
  where I: Input,
        P: Parser<I> {
    type Output = P::Output;
    type Error  = P::Error;

    #[cfg_attr(feature="clippy", allow(boxed_local))]
    #[inline]
    fn parse_box(self: Box<Self>, i: I) -> (I, Result<P::Output, P::Error>) {
        (*self).parse(i)
    }
}

impl<I, T, E> Parser<I> for Box<BoxParser<I, Output=T, Error=E>>
  where I: Input {
    type Output = T;
    type Error  = E;

    #[inline]
    fn parse(self, i: I) -> (I, Result<T, E>) {
        self.parse_box(i)
    }
}

/// Returns `t` as a success value in the parsing context.
///
/// Equivalent to Haskell's `return` function in the `Monad` typeclass.
///
/// # Example
///
/// ```
/// use chomp::types::ret;
/// use chomp::parse_only;
///
/// let r = parse_only(
///     // Annotate the error type
///     ret::<_, ()>("Wohoo, success!"),
///     b"some input");
///
/// assert_eq!(r, Ok("Wohoo, success!"));
/// ```
#[inline]
pub fn ret<T, E>(t: T) -> RetParser<T, E> {
    RetParser { t: t, _e: PhantomData }
}

/// Returns `e` as an error value in the parsing context.
///
/// A more general version of Haskell's `fail` function in the `Monad` typeclass.
///
/// # Example
///
/// ```
/// use chomp::types::err;
/// use chomp::parse_only;
///
/// let r = parse_only(
///     // Annotate the value type
///     err::<(), _>("Something went wrong"),
///     b"some input");
///
/// assert_eq!(r, Err((&b"some input"[..], "Something went wrong")));
/// ```
#[inline]
pub fn err<T, E>(e: E) -> ErrParser<T, E> {
    ErrParser { e: e, _t: PhantomData }
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
/// use chomp::types::from_result;
/// use chomp::parse_only;
///
/// let r = parse_only(from_result::<_, ()>(Ok("foo")), b"test");
///
/// assert_eq!(r, Ok("foo"));
///
/// let r = parse_only(from_result::<(), _>(Err("error message")), b"test");
///
/// assert_eq!(r, Err((&b"test"[..], "error message")));
/// ```
#[inline]
pub fn from_result<T, E>(r: Result<T, E>) -> FromResultParser<T, E> {
    FromResultParser { r: r }
}

/// Parser containing a success value.
///
/// This is created by `ret`.
#[derive(Debug)]
pub struct RetParser<T, E> {
    t:  T,
    _e: PhantomData<E>,
}

impl<I, T, E> Parser<I> for RetParser<T, E>
  where I: Input {
    type Output = T;
    type Error  = E;

    #[inline]
    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        (i, Ok(self.t))
    }
}

/// Parser containing an error value.
///
/// This is created by `err`.
#[derive(Debug)]
pub struct ErrParser<T, E> {
    e:  E,
    _t: PhantomData<T>,
}

impl<I, T, E> Parser<I> for ErrParser<T, E>
  where I: Input {
    type Output = T;
    type Error  = E;

    #[inline]
    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        (i, Err(self.e))
    }
}

/// Parser containing a `Result<T, E>`.
///
/// This is created by `from_result`.
#[derive(Debug)]
pub struct FromResultParser<T, E> {
    r:  Result<T, E>,
}

impl<I, T, E> Parser<I> for FromResultParser<T, E>
  where I: Input {
    type Output = T;
    type Error  = E;

    #[inline]
    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        (i, self.r)
    }
}

/// Parser for the `Parser::bind` chaining operator, allowing to chain parsers.
///
/// This is created by the `Parser::bind` method.
#[derive(Debug)]
pub struct BindParser<I, P, F, R>
  where I: Input,
        P: Parser<I>,
        F: FnOnce(P::Output) -> R,
        R: Parser<I, Error=P::Error> {
    p:  P,
    f:  F,
    // Necessary for inference, if we do not have I here we cannot describe the return value of `F`
    // and this would make it impossible for rustc to infer the type of the created parser.
    _i: PhantomData<I>,
}

impl<I, P, F, R> Parser<I> for BindParser<I, P, F, R>
  where I: Input,
        P: Parser<I>,
        F: FnOnce(P::Output) -> R,
        R: Parser<I, Error=P::Error> {
    type Output = R::Output;
    type Error  = R::Error;

    #[inline]
    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        match self.p.parse(i) {
            (r, Ok(t))  => (self.f)(t).parse(r),
            (r, Err(e)) => (r, Err(e)),
        }
    }
}

/// Parser for the `Parser::then` chaining operator, allowing to chain parsers.
///
/// This is created by the `Parser::then` method.
#[derive(Debug)]
pub struct ThenParser<I, P, Q> {
    p:  P,
    q:  Q,
    _i: PhantomData<I>,
}

impl<I, P, Q> Parser<I> for ThenParser<I, P, Q>
  where I: Input,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error> {
    type Output = Q::Output;
    type Error  = Q::Error;

    #[inline]
    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        match self.p.parse(i) {
            (r, Ok(_))  => (self.q).parse(r),
            (r, Err(e)) => (r, Err(e)),
        }
    }
}

/// Parser for the `Parser::map` combinator.
///
/// This is created by the `Parser::map` method.
#[derive(Debug)]
pub struct MapParser<I, P, F> {
    p:  P,
    f:  F,
    _i: PhantomData<I>,
}

impl<I, P, F, R> Parser<I> for MapParser<I, P, F>
  where I: Input,
        P: Parser<I>,
        F: FnOnce(P::Output) -> R {
    type Output = R;
    type Error  = P::Error;

    #[inline]
    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        match self.p.parse(i) {
            (r, Ok(t))  => (r, Ok((self.f)(t))),
            (r, Err(e)) => (r, Err(e)),
        }
    }
}

/// Parser for the `Parser::map_err` combinator.
///
/// This is created by the `Parser::map_err` method.
#[derive(Debug)]
pub struct MapErrParser<I, P, F> {
    p:  P,
    f:  F,
    _i: PhantomData<I>
}

impl<I, P, F, E> Parser<I> for MapErrParser<I, P, F>
  where I: Input,
        P: Parser<I>,
        F: FnOnce(P::Error) -> E {
    type Output = P::Output;
    type Error  = E;

    #[inline]
    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        match self.p.parse(i) {
            (r, Ok(t))  => (r, Ok(t)),
            (r, Err(e)) => (r, Err((self.f)(e))),
        }
    }
}

/// Parser for the `Parser::inspect` combinator.
///
/// This is created by `Parser::inspect`.
#[derive(Debug)]
pub struct InspectParser<I, P, F> {
    p:  P,
    f:  F,
    _i: PhantomData<I>,
}

impl<I, P, F> Parser<I> for InspectParser<I, P, F>
  where I: Input,
        P: Parser<I>,
        F: FnOnce(&P::Output) {
    type Output = P::Output;
    type Error  = P::Error;

    #[inline]
    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        match self.p.parse(i) {
            (r, Ok(t))      => {
                (self.f)(&t);

                (r, Ok(t))
            },
            (r, Err(e)) => (r, Err(e)),
        }
    }
}

/// Parser for the `Parser::or` combinator.
///
/// This is created by `Parser::or`.
#[derive(Debug)]
pub struct OrParser<I, P, Q> {
    p:  P,
    q:  Q,
    _i: PhantomData<I>,
}

impl<I, P, Q> Parser<I> for OrParser<I, P, Q>
  where I: Input,
        P: Parser<I>,
        Q: Parser<I, Output=P::Output, Error=P::Error> {
    type Output = P::Output;
    type Error  = P::Error;

    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        let m = i.mark();

        match self.p.parse(i) {
            (r, Ok(d))  => (r, Ok(d)),
            (r, Err(_)) => self.q.parse(r.restore(m)),
        }
    }
}

/// Parser for the `Parser::skip` combinator.
///
/// This is created by `Parser::skip`.
#[derive(Debug)]
pub struct SkipParser<I, P, Q> {
    p:  P,
    q:  Q,
    _i: PhantomData<I>,
}

impl<I, P, Q> Parser<I> for SkipParser<I, P, Q>
  where I: Input,
        P: Parser<I>,
        Q: Parser<I, Error=P::Error> {
    type Output = P::Output;
    type Error  = P::Error;

    fn parse(self, i: I) -> (I, Result<Self::Output, Self::Error>) {
        // Merge of p.bind(|t| q.map(|_| t))
        match self.p.parse(i) {
            (r, Ok(t))  => match self.q.parse(r) {
                (b, Ok(_))  => (b, Ok(t)),
                (b, Err(e)) => (b, Err(e)),
            },
            (r, Err(e)) => (r, Err(e)),
        }
    }
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

#[cfg(test)]
pub mod test {
    use super::{Buffer, Input, Parser, ret, err, from_result};
    use std::fmt::Debug;

    #[test]
    fn ret_test() {
        assert_eq!(ret::<_, ()>(23u32).parse(&b"in1"[..]), (&b"in1"[..], Ok(23u32)));
        assert_eq!(ret::<_, &str>(23i32).parse(&b"in2"[..]), (&b"in2"[..], Ok(23i32)));
    }

    #[test]
    fn err_test() {
        assert_eq!(err::<(), _>(23u32).parse(&b"in1"[..]), (&b"in1"[..], Err(23u32)));
        assert_eq!(err::<&str, _>(23i32).parse(&b"in2"[..]), (&b"in2"[..], Err(23i32)));
    }

    #[test]
    fn from_result_test() {
        let i1: Result<u32, &str> = Ok(23);
        let i2: Result<&str, &str> = Err("foobar");

        assert_eq!(from_result(i1).parse(&b"in1"[..]), (&b"in1"[..], Ok(23u32)));
        assert_eq!(from_result(i2).parse(&b"in2"[..]), (&b"in2"[..], Err("foobar")));
    }

    #[test]
    fn monad_left_identity() {
        fn f<I: Input>(n: u32) -> impl Parser<I, Output=u32, Error=()> {
            ret(n + 1)
        }

        let a = 123;
        // return a >>= f
        let lhs = ret(a).bind(f);
        // f a
        let rhs = f(a);

        assert_eq!(lhs.parse(&b"test"[..]), (&b"test"[..], Ok(124)));
        assert_eq!(rhs.parse(&b"test"[..]), (&b"test"[..], Ok(124)));
    }

    #[test]
    fn monad_right_identity() {
        let m1 = ret::<_, ()>(1);
        let m2 = ret::<_, ()>(1);

        // m1 >>= ret === m2
        let lhs = m1.bind(ret);
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

        let lhs_m = ret::<_, ()>(2);
        let rhs_m = ret::<_, ()>(2);

        // (m >>= f) >>= g
        let lhs = lhs_m.bind(f).bind(g);
        // m >>= (\x -> f x >>= g)
        let rhs = rhs_m.bind(|x| f(x).bind(g));

        assert_eq!(lhs.parse(&b"test"[..]), (&b"test"[..], Ok(6)));
        assert_eq!(rhs.parse(&b"test"[..]), (&b"test"[..], Ok(6)));
    }

    #[test]
    fn or_test() {
        use parsers::{Error, any, take, token};

        assert_eq!(any().or(any()).parse(&b""[..]), (&b""[..], Err(Error::unexpected())));
        assert_eq!(any().or(any()).parse(&b"a"[..]), (&b""[..], Ok(b'a')));
        assert_eq!(take(2).or(take(1)).parse(&b"a"[..]), (&b""[..], Ok(&b"a"[..])));
        assert_eq!(take(2).or(take(1)).parse(&b"ab"[..]), (&b""[..], Ok(&b"ab"[..])));
        assert_eq!(token(b'a').or(token(b'b')).parse(&b"a"[..]), (&b""[..], Ok(b'a')));
        assert_eq!(token(b'a').or(token(b'b')).parse(&b"b"[..]), (&b""[..], Ok(b'b')));
        assert_eq!(token(b'a').map_err(|_| "a err").or(token(b'b').map_err(|_| "b err")).parse(&b"c"[..]), (&b"c"[..], Err("b err")));
    }

    // TODO: More tests for fundamental combinators implemented on Parser

    #[test]
    fn parse_result_inspect() {
        let mut n1 = 0;
        let mut n2 = 0;

        {
            let i1     = ret::<u32, ()>(23);
            let i2     = ret::<u32, ()>(23);
            let i3     = err::<u32, i32>(42);

            let r1 = i1.inspect(|d: &u32| {
                assert_eq!(d, &23);

                n1 += 1;
            });
            let r2 = i2.inspect(|d: &u32| {
                assert_eq!(d, &23);

                n2 += 1;
            });
            let r3 = i3.inspect(|_: &u32| {
                panic!("Success value obtained in error branch in inspect!");
            });

            assert_eq!(r1.parse(&b"test"[..]), (&b"test"[..], Ok(23)));
            assert_eq!(r2.parse(&b"test"[..]), (&b"test"[..], Ok(23)));
            assert_eq!(r3.parse(&b"test"[..]), (&b"test"[..], Err(42)));
        }

        assert_eq!(n1, 1);
        assert_eq!(n2, 1);
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
