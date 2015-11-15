//! Module used to construct fundamental parsers and combinators.

use ::{Data, Input};

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

/// Trait for modifying `Data`.
/// 
/// Only use this to create fundamental combinators.
pub trait DataModify<'a> {
    type Input;
    type Data;
    type Error;

    /// Modifies the content of Data, without changing its type.
    #[inline(always)]
    fn modify<F>(self, F) -> Self
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>) -> Data<'a, Self::Input, Self::Data, Self::Error>,
            <Self as DataModify<'a>>::Input: 'a,
            <Self as DataModify<'a>>::Data:  'a,
            <Self as DataModify<'a>>::Error: 'a;

    /// Modifies the content of Data, allowing types to change.
    // TODO: Is this needed?
    #[inline(always)]
    fn parse<I, T, E, F>(self, F) -> Data<'a, I, T, E>
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>) -> Data<'a, I, T, E>,
            <Self as DataModify<'a>>::Input: 'a,
            <Self as DataModify<'a>>::Data:  'a,
            <Self as DataModify<'a>>::Error: 'a;

    /// Consumes the `Data` and reveals the inner state.
    #[inline(always)]
    fn internal(self) -> State<'a, Self::Input, Self::Data, Self::Error>;
}

impl<'a, I, T, E> DataModify<'a> for Data<'a, I, T, E> {
    type Input = I;
    type Data  = T;
    type Error = E;

    #[inline(always)]
    fn modify<F>(self, f: F) -> Self
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>) -> Data<'a, Self::Input, Self::Data, Self::Error>,
            <Self as DataModify<'a>>::Input: 'a,
            <Self as DataModify<'a>>::Data:  'a,
            <Self as DataModify<'a>>::Error: 'a {
        f(self.0)
    }

    #[inline(always)]
    fn parse<N, Y, R, F>(self, f: F) -> Data<'a, N, Y, R>
      where F: FnOnce(State<'a, Self::Input, Self::Data, Self::Error>) -> Data<'a, N, Y, R>,
            <Self as DataModify<'a>>::Input: 'a,
            <Self as DataModify<'a>>::Data:  'a,
            <Self as DataModify<'a>>::Error: 'a {
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
    fn parse<F, T, E>(self, f: F) -> Data<'a, Self::Type, T, E>
      where F: FnOnce(&'a [Self::Type]) -> Data<'a, Self::Type, T, E>,
            <Self as InputModify<'a>>::Type: 'a;
}

/// Creates a data-carrying value from an input slice and a data value.
#[inline(always)]
pub fn data<'a, I, T, E>(i: &'a [I], t: T) -> Data<'a, I, T, E> {
    Data(State::Data(i, t))
}

/// Creates an error value from an input slice and an error value.
#[inline(always)]
pub fn error<'a, I, T, E>(i: &'a [I], e: E) -> Data<'a, I, T, E> {
    Data(State::Error(i, e))
}

/// Notifies the combinator that a parser has reached the end of the currently supplied slice but
/// requires more data.
#[inline(always)]
pub fn incomplete<'a, I, T, E>(n: usize) -> Data<'a, I, T, E> {
    Data(State::Incomplete(n))
}

impl<'a, I> InputModify<'a> for Input<'a, I> {
    type Type = I;

    #[inline(always)]
    fn modify<F>(self, f: F) -> Self
      where F: FnOnce(&'a [Self::Type]) -> &'a [Self::Type] {
        Input(f(self.0))
    }

    #[inline(always)]
    fn parse<F, T, E>(self, f: F) -> Data<'a, Self::Type, T, E>
      where F: FnOnce(&'a [Self::Type]) -> Data<'a, Self::Type, T, E> {
        f(self.0)
    }
}

