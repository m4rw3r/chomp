//! Module used to construct fundamental parsers and combinators.

use ::{ParseResult, Input};

/// Private inner type containing the parse-state.
/// 
/// Only used to create fundamental parsers and combinators.
#[must_use]
#[derive(Debug, Eq, PartialEq)]
pub enum State<'a, I: 'a, T, E>
  where I: 'a,
        T: 'a,
        E: 'a {
    Data(&'a [I], T),
    Error(&'a [I], E),
    Incomplete(usize),
}

/// Trait for modifying `ParseResult`.
/// 
/// Only use this to create fundamental combinators.
pub trait ParseResultModify<'a> {
    type Input;
    type Data;
    type Error;

    /// Modifies the content of ParseResult, without changing its type.
    #[inline(always)]
    fn modify<F>(self, F) -> Self
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>) -> ParseResult<'a, Self::Input, Self::Data, Self::Error>,
            <Self as ParseResultModify<'a>>::Input: 'a,
            <Self as ParseResultModify<'a>>::Data:  'a,
            <Self as ParseResultModify<'a>>::Error: 'a;

    /// Modifies the content of ParseResult, allowing types to change.
    // TODO: Is this needed?
    #[inline(always)]
    fn parse<I, T, E, F>(self, F) -> ParseResult<'a, I, T, E>
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>) -> ParseResult<'a, I, T, E>,
            <Self as ParseResultModify<'a>>::Input: 'a,
            <Self as ParseResultModify<'a>>::Data:  'a,
            <Self as ParseResultModify<'a>>::Error: 'a;

    /// Consumes the `ParseResult` and reveals the inner state.
    #[inline(always)]
    fn internal(self) -> State<'a, Self::Input, Self::Data, Self::Error>;
}

impl<'a, I, T, E> ParseResultModify<'a> for ParseResult<'a, I, T, E> {
    type Input = I;
    type Data  = T;
    type Error = E;

    #[inline(always)]
    fn modify<F>(self, f: F) -> Self
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>) -> ParseResult<'a, Self::Input, Self::Data, Self::Error>,
            <Self as ParseResultModify<'a>>::Input: 'a,
            <Self as ParseResultModify<'a>>::Data:  'a,
            <Self as ParseResultModify<'a>>::Error: 'a {
        f(self.0)
    }

    #[inline(always)]
    fn parse<N, Y, R, F>(self, f: F) -> ParseResult<'a, N, Y, R>
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>) -> ParseResult<'a, N, Y, R>,
            <Self as ParseResultModify<'a>>::Input: 'a,
            <Self as ParseResultModify<'a>>::Data:  'a,
            <Self as ParseResultModify<'a>>::Error: 'a {
        f(self.0)
    }

    #[inline(always)]
    fn internal(self) -> State<'a, Self::Input, Self::Data, Self::Error> {
        self.0
    }
}

/// Trait for modifying `Input`.
/// 
/// Only use this to create fundamental parsers and combinators.
pub trait InputModify<'a> {
    type Type;

    /// Modifies the inner data without leaving the `Input` context.
    #[inline(always)]
    fn modify<F>(self, f: F) -> Self
      where F: FnOnce(&'a [Self::Type]) -> &'a [Self::Type],
            <Self as InputModify<'a>>::Type: 'a;

    /// Applies a parser operating directly on &[Type] to the input.
    #[inline(always)]
    fn parse<F, T, E>(self, f: F) -> ParseResult<'a, Self::Type, T, E>
      where F: FnOnce(&'a [Self::Type]) -> ParseResult<'a, Self::Type, T, E>,
            <Self as InputModify<'a>>::Type: 'a;
}

/// Creates a data-carrying value from an input slice and a data value.
#[inline(always)]
pub fn data<'a, I, T, E>(i: &'a [I], t: T) -> ParseResult<'a, I, T, E> {
    ParseResult(State::Data(i, t))
}

/// Creates an error value from an input slice and an error value.
#[inline(always)]
pub fn error<'a, I, T, E>(i: &'a [I], e: E) -> ParseResult<'a, I, T, E> {
    ParseResult(State::Error(i, e))
}

/// Notifies the combinator that a parser has reached the end of the currently supplied slice but
/// requires more data.
#[inline(always)]
pub fn incomplete<'a, I, T, E>(n: usize) -> ParseResult<'a, I, T, E> {
    ParseResult(State::Incomplete(n))
}

impl<'a, I> InputModify<'a> for Input<'a, I> {
    type Type = I;

    #[inline(always)]
    fn modify<F>(self, f: F) -> Self
      where F: FnOnce(&'a [Self::Type]) -> &'a [Self::Type] {
        Input(f(self.0))
    }

    #[inline(always)]
    fn parse<F, T, E>(self, f: F) -> ParseResult<'a, Self::Type, T, E>
      where F: FnOnce(&'a [Self::Type]) -> ParseResult<'a, Self::Type, T, E> {
        f(self.0)
    }
}

