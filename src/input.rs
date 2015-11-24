use ParseResult;
use internal::State;
use parse_result;
use internal::{
    InputClone,
    InputBuffer,
};

bitflags!{
    flags InputMode: u32 {
        /// Default (empty) input state.
        const DEFAULT      = 0,
        /// If set the current slice of input is the last one.
        const END_OF_INPUT = 1,
    }
}

/// Linear type containing the parser state, this type is threaded though `bind`.
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Input<'a, I: 'a>(InputMode, &'a [I]);

/// Creates a new input from the given state and buffer.
///
/// # Internal
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
    /// # Internal
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

impl<'a, I: 'a> InputClone for Input<'a, I> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Input(self.0, self.1)
    }
}

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
