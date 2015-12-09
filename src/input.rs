use parse_result::{ParseResult, State};
use parse_result;

bitflags!{
    flags InputMode: u32 {
        /// Default (empty) input state.
        const DEFAULT      = 0,
        /// If set the current slice of input is the last one.
        const END_OF_INPUT = 1,
    }
}

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
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Input<'a, I: 'a>(InputMode, &'a [I]);

/// **Primitive:** Creates a new input from the given state and buffer.
///
/// # Primitive
///
/// Only used by fundamental parsers and combinators.
pub fn new<I>(state: InputMode, buffer: &[I]) -> Input<I> {
    Input(state, buffer)
}

impl<'a, I> Input<'a, I> {
    /// Creates a new `Input` to start parsing with.
    ///
    /// # Note
    ///
    /// This should only be used for simple examples, for anything more advanced look at the
    /// `buffer` module.
    // TODO: Remove, use parse_slice instead
    #[inline]
    pub fn new(b: &'a [I]) -> Self {
        Input(END_OF_INPUT, b)
    }

    /// Returns `t` as a success value in the parsing context.
    ///
    /// Equivalent to Haskell's `return` function in the `Monad` typeclass.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::Input;
    ///
    /// let i = Input::new(b"some state");
    ///
    /// // Annotate the error type
    /// let r = i.ret::<_, ()>("Wohoo, success!");
    ///
    /// assert_eq!(r.unwrap(), "Wohoo, success!");
    /// ```
    #[inline]
    pub fn ret<T, E = ()>(self, t: T) -> ParseResult<'a, I, T, E> {
        parse_result::new(State::Data(self, t))
    }

    /// Returns `e` as an error value in the parsing context.
    ///
    /// A more general version of Haskell's `fail` function in the `Monad` typeclass.
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::Input;
    ///
    /// let i = Input::new(b"some state");
    ///
    /// // Annotate the value type
    /// let r = i.err::<(), _>("Something went wrong");
    ///
    /// assert_eq!(r.unwrap_err(), "Something went wrong");
    /// ```
    #[inline]
    pub fn err<T, E>(self, e: E) -> ParseResult<'a, I, T, E> {
        parse_result::new(State::Error(self.1, e))
    }

    /// Notifies that a parser has reached the end of the currently supplied slice but requires
    /// more data.
    ///
    /// # Primitive
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline]
    pub fn incomplete<T, E>(self, n: usize) -> ParseResult<'a, I, T, E> {
        parse_result::new(State::Incomplete(n))
    }

    /// Converts a `Result` into a `ParseResult`, preserving parser state.
    ///
    /// # Examples
    ///
    /// ```
    /// use chomp::Input;
    ///
    /// let r = Input::new(b"test").from_result::<_, ()>(Ok("foo"));
    ///
    /// assert_eq!(r.unwrap(), "foo");
    /// ```
    ///
    /// ```
    /// use chomp::Input;
    ///
    /// let r = Input::new(b"test").from_result::<(), _>(Err("error message"));
    ///
    /// assert_eq!(r.unwrap_err(), "error message");
    /// ```
    #[inline]
    pub fn from_result<T, E>(self, r: Result<T, E>) -> ParseResult<'a, I, T, E> {
        match r {
            Ok(t)  => parse_result::new(State::Data(self, t)),
            Err(e) => parse_result::new(State::Error(self.1, e)),
        }
    }
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
///
/// # Example
///
/// ```
/// use chomp::{Input, take};
/// use chomp::primitives::InputBuffer;
///
/// let i = Input::new(b"Testing");
///
/// assert_eq!(i.buffer(), b"Testing");
/// assert_eq!(i.is_last_slice(), true);
///
/// let b = i.buffer();
/// let j = i.replace(&b[..4]);
///
/// let r = take(j, 4);
///
/// assert_eq!(r.unwrap(), b"Test");
/// ```
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

#[cfg(feature = "nom_adapter")]
impl<'a, I> Input<'a, I> {
    /// Calls out to a Nom parser.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate chomp;
    /// #[macro_use]
    /// extern crate nom;
    ///
    /// use chomp::{Input, ParseResult};
    /// use chomp::{take_while1, token, take_remainder};
    /// use chomp::ascii::is_alpha;
    ///
    /// named!(nom_word, chain!(word: take_while1!(is_alpha) ~ tag!(b" "), || word));
    ///
    /// # fn main() {
    ///     let i = Input::new(b"Works with Nom!");
    ///
    ///     let r: ParseResult<_, _, chomp::NomError<_, _>> = parse!{i;
    ///         let first      = take_while1(is_alpha);
    ///                          token(b' ');
    ///         let nom_result = i -> i.nom_parser(nom_word);
    ///         let remainder  = take_remainder();
    ///
    ///         ret (first, nom_result, remainder)
    ///     };
    ///
    ///     assert_eq!(r.unwrap(), (&b"Works"[..], &b"with"[..], &b"Nom!"[..]));
    /// # }
    /// ```
    pub fn nom_parser<T, E, F>(self, f: F) -> ParseResult<'a, I, T, NomError<'a, I, E>>
      where F: FnOnce(&'a [I]) -> ::nom::IResult<&'a [I], T, E> {
        use nom::IResult;
        use nom::Needed;

        match f(self.1) {
            IResult::Done(b, t)                  => parse_result::new(State::Data(Input(self.0, b), t)),
            IResult::Error(e)                    => parse_result::new(State::Error(self.1, NomError::NomError(e))),
            IResult::Incomplete(Needed::Unknown) => parse_result::new(State::Incomplete(1)),
            IResult::Incomplete(Needed::Size(n)) => parse_result::new(State::Incomplete(n)),
        }
    }
}

#[cfg(feature = "nom_adapter")]
#[derive(Debug)]
pub enum NomError<'a, I: 'a, E> {
    NomError(::nom::Err<&'a [I], E>),
    ChompError(::parsers::Error<I>),
}

#[cfg(feature = "nom_adapter")]
impl<'a, I: 'a, E> From<::nom::Err<&'a [I], E>> for NomError<'a, I, E> {
    fn from(e: ::nom::Err<&'a [I], E>) -> Self {
        NomError::NomError(e)
    }
}

#[cfg(feature = "nom_adapter")]
impl<'a, I, E> From<::parsers::Error<I>> for NomError<'a, I, E> {
    fn from(e: ::parsers::Error<I>) -> Self {
        NomError::ChompError(e)
    }
}

#[cfg(test)]
mod test {
    use super::{new, Input, InputBuffer, DEFAULT, END_OF_INPUT};
    use parse_result::ParseResult;
    use primitives::{IntoInner, State};

    #[test]
    fn make_ret() {
        let i1: Input<u8> = new(END_OF_INPUT, b"in1");
        let i2: Input<u8> = new(DEFAULT,      b"in2");

        let r1: ParseResult<u8, u32, ()> = i1.ret::<_, ()>(23u32);
        let r2: ParseResult<u8, i32, ()> = i2.ret::<_, ()>(23i32);

        assert_eq!(r1.into_inner(), State::Data(Input(END_OF_INPUT, b"in1"), 23u32));
        assert_eq!(r2.into_inner(), State::Data(Input(DEFAULT, b"in2"), 23i32));
    }

    #[test]
    fn make_err() {
        let i1: Input<u8> = new(END_OF_INPUT, b"in1");
        let i2: Input<u8> = new(DEFAULT,      b"in2");

        let r1: ParseResult<u8, (), u32> = i1.err::<(), _>(23u32);
        let r2: ParseResult<u8, (), i32> = i2.err::<(), _>(23i32);

        assert_eq!(r1.into_inner(), State::Error(b"in1", 23u32));
        assert_eq!(r2.into_inner(), State::Error(b"in2", 23i32));
    }

    #[test]
    fn make_incomplete() {
        let i1: Input<u8> = new(END_OF_INPUT, b"in1");
        let i2: Input<u8> = new(DEFAULT,      b"in2");

        let r1: ParseResult<u8, (), u32> = i1.incomplete::<(), _>(23);
        let r2: ParseResult<u8, (), i32> = i2.incomplete::<(), _>(23);

        assert_eq!(r1.into_inner(), State::Incomplete(23));
        assert_eq!(r2.into_inner(), State::Incomplete(23));
    }

    #[test]
    fn last_slice() {
        let i = new(END_OF_INPUT, &b"foo"[..]);

        assert_eq!(i.is_last_slice(), true);
    }
}
