//! Module used to construct fundamental parsers and combinators.
//!
//! # Internal
//!
//! Only used by fundamental parsers and combinators.

use {ParseResult, Input};

/// Internal inner type containing the parse-state.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum State<'a, I: 'a, T, E>
  where I: 'a,
        T: 'a,
        E: 'a {
    Data(Input<'a, I>, T),
    Error(&'a [I], E),
    Incomplete(usize),
}

/// Internal trait for modifying `ParseResult`.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
pub trait ParseResultModify<'a> {
    type Input;
    type Data;
    type Error;

    /// Modifies the content of ParseResult, without changing its type.
    #[inline(always)]
    fn modify<F>(self, F) -> Self
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>)
                   -> ParseResult<'a, Self::Input, Self::Data, Self::Error>,
            <Self as ParseResultModify<'a>>::Input: 'a,
            <Self as ParseResultModify<'a>>::Data:  'a,
            <Self as ParseResultModify<'a>>::Error: 'a;

    /// Applies the function `f` to the inner `State`, allows modification of data and error types.
    #[inline(always)]
    fn parse<F, T, E>(self, F) -> ParseResult<'a, Self::Input, T, E>
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>)
                   -> ParseResult<'a, Self::Input, T, E>,
            <Self as ParseResultModify<'a>>::Input: 'a,
            <Self as ParseResultModify<'a>>::Data:  'a,
            <Self as ParseResultModify<'a>>::Error: 'a;

    /// Consumes the `ParseResult` and reveals the inner state.
    #[inline(always)]
    fn internal(self) -> State<'a, Self::Input, Self::Data, Self::Error>;
}

/// Implementation of internal trait used as a building block for combinators.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
impl<'a, I, T, E> ParseResultModify<'a> for ParseResult<'a, I, T, E> {
    type Input = I;
    type Data  = T;
    type Error = E;

    /// Applies the function `f` to the inner `State` while preserving types.
    #[inline(always)]
    fn modify<F>(self, f: F) -> Self
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>)
                   -> ParseResult<'a, Self::Input, Self::Data, Self::Error>,
            <Self as ParseResultModify<'a>>::Input: 'a,
            <Self as ParseResultModify<'a>>::Data:  'a,
            <Self as ParseResultModify<'a>>::Error: 'a {
        f(self.0)
    }

    /// Applies the function `f` to the inner `State`, allows modification of data and error types.
    #[inline(always)]
    fn parse<F, U, V>(self, f: F) -> ParseResult<'a, Self::Input, U, V>
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>)
                   -> ParseResult<'a, Self::Input, U, V>,
            <Self as ParseResultModify<'a>>::Input: 'a,
            <Self as ParseResultModify<'a>>::Data:  'a,
            <Self as ParseResultModify<'a>>::Error: 'a {
        f(self.0)
    }

    /// Consumes the `ParseResult` and reveals the inner state.
    #[inline(always)]
    fn internal(self) -> State<'a, Self::Input, Self::Data, Self::Error> {
        self.0
    }
}

/// Input utilities.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
pub mod input {
    pub const DEFAULT: u32      = 0;
    pub const END_OF_INPUT: u32 = 1;
}

/// Trait for modifying `Input`.
///
/// # Internal
///
/// Only used by fundamental parsers and combinators.
pub trait InputModify<'a> {
    type Type;

    /// Creates a clone of the instance.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(Always)]
    fn clone_input(&self) -> Self;

    /// Reveals the internal buffer containig the remainder of the input.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn buffer(&self) -> &'a [Self::Type]
      where <Self as InputModify<'a>>::Type: 'a;

    /// Modifies the inner data without leaving the `Input` context.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn replace(self, &'a [Self::Type]) -> Self
      where <Self as InputModify<'a>>::Type: 'a;

    /// Modifies the inner data without leaving the `Input` context.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn modify<F>(self, F) -> Self
      where F: Fn(&'a [Self::Type]) -> &'a [Self::Type],
          <Self as InputModify<'a>>::Type: 'a;

    /// Creates a data-carrying value from an input slice and a data value.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn data<T, E>(self, T) -> ParseResult<'a, Self::Type, T, E>;

    /// Creates an error value from an input slice and an error value.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn error<T, E>(self, E) -> ParseResult<'a, Self::Type, T, E>;

    /// Notifies the combinator that a parser has reached the end of the currently supplied slice but
    /// requires more data.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn incomplete<T, E>(self, usize) -> ParseResult<'a, Self::Type, T, E>;

    /// Returns true if this is the last available slice of the input.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn is_last_slice(&self) -> bool;
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

    /// Creates a data-carrying value from an input slice and a data value.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    // TODO: Remove; use ret instead
    fn data<T, E>(self, t: T) -> ParseResult<'a, Self::Type, T, E> {
        ParseResult(State::Data(self, t))
    }

    /// Creates an error value from an input slice and an error value.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    // TODO: Remove; use err instead
    fn error<T, E>(self, e: E) -> ParseResult<'a, Self::Type, T, E> {
        ParseResult(State::Error(self.1, e))
    }

    /// Notifies the combinator that a parser has reached the end of the currently supplied slice but
    /// requires more data.
    ///
    /// # Internal
    ///
    /// Only used by fundamental parsers and combinators.
    #[inline(always)]
    fn incomplete<T, E>(self, n: usize) -> ParseResult<'a, Self::Type, T, E> {
        ParseResult(State::Incomplete(n))
    }

    #[inline(always)]
    fn is_last_slice(&self) -> bool {
        self.0 & input::END_OF_INPUT == input::END_OF_INPUT
    }
}
