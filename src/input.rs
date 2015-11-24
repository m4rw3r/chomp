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

/// Linear type containing the parser state, this type is threaded though `bind`.
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
    // TODO: Remove, use parse_slice instead
    pub fn new(b: &'a [I]) -> Self {
        Input(END_OF_INPUT, b)
    }

    /// Returns the value `t` with the input context.
    #[inline]
    pub fn ret<T, E>(self, t: T) -> ParseResult<'a, I, T, E> {
        parse_result::new(State::Data(self, t))
    }

    /// Returns the error value `e` with the input context.
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

    /// Converts a `Result` into a `ParseResult`.
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
