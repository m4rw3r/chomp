use ParseResult;
use internal::State;
use internal::InputModify;
use parse_result;

/// Default (empty) input state.
pub const DEFAULT: u32      = 0;
/// If set the current slice of input is the last one.
pub const END_OF_INPUT: u32 = 1;

/// Linear type containing the parser state, this type is threaded though `bind`.
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Input<'a, I: 'a>(u32, &'a [I]);

/// Creates a new input from the given state and buffer.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
pub fn new<I>(state: u32, buffer: &[I]) -> Input<I> {
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

/// Implementation of internal trait used to build parsers and combinators.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
impl<'a, I> InputModify<'a> for Input<'a, I> {
    type Type = I;

    /// Creates a clone of the instance.
    #[inline(always)]
    fn clone_input(&self) -> Self {
        Input(self.0, self.1)
    }

    #[inline(always)]
    fn buffer(&self) -> &'a [Self::Type]
      where <Self as InputModify<'a>>::Type: 'a {
        self.1
    }

    /// Modifies the inner data without leaving the `Input` context.
    #[inline(always)]
    fn replace(self, b: &'a [Self::Type]) -> Self
      where <Self as InputModify<'a>>::Type: 'a {
        Input(self.0, b)
    }

    /// Modifies the inner data without leaving the `Input` context.
    #[inline(always)]
    fn modify<F>(self, f: F) -> Self
      where F: Fn(&'a [Self::Type]) -> &'a [Self::Type],
          <Self as InputModify<'a>>::Type: 'a {
        Input(self.0, f(self.1))
    }

    /// Notifies the combinator that a parser has reached the end of the currently supplied slice but
    /// requires more data.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn incomplete<T, E>(self, n: usize) -> ParseResult<'a, Self::Type, T, E> {
        parse_result::new(State::Incomplete(n))
    }

    /// Returns true if this is the last input slice available.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn is_last_slice(&self) -> bool {
        self.0 & END_OF_INPUT == END_OF_INPUT
    }
}
