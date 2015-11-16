//! Library providing a parser combinator.
//!
//! ```
//! use chomp::{Input, ParseResult, Error};
//! use chomp::{take_while1, token};
//!
//! let i = Input::new("martin wernstål\n".as_bytes());
//! 
//! #[derive(Debug, Eq, PartialEq)]
//! struct Name<'a> {
//!     first: &'a [u8],
//!     last:  &'a [u8],
//! }
//! 
//! fn name(i: Input<u8>) -> ParseResult<u8, Name, Error<u8>> {
//!     take_while1(i, |c| c != b' ').bind(|i, first|
//!         token(i, b' ').bind(|i, _| // skipping this char
//!             take_while1(i, |c| c != b'\n').bind(|i, last|
//!                 i.ret(Name{
//!                     first: first,
//!                     last:  last,
//!                 }))))
//! }
//! 
//! assert_eq!(name(i).unwrap(), Name{first: b"martin", last: "wernstål".as_bytes()});
//! ```
use ::std::fmt;

#[macro_use]
mod macros;
mod iter;

pub mod internal;
pub mod parsers;
pub mod combinators;

pub use combinators::{
    count,
    option,
    or,
    many,
    many1,
    skip_many,
};
pub use parsers::{
    any,
    not_token,
    peek,
    satisfy,
    string,
    take,
    take_remainder,
    take_till,
    take_while,
    take_while1,
    token,
};
pub use err::Error;
pub use iter::Iter;

use internal::State;

/// Linear type containing the parser state, this type is threaded though `bind`.
#[must_use]
#[derive(Debug, Eq, PartialEq)]
pub struct Input<'a, I: 'a>(&'a [I]);

impl<'a, I> Input<'a, I> {
    /// Creates a new input to be passed to parsers and/or combinators.
    pub fn new(i: &'a [I]) -> Self {
        Input(i)
    }

    /// Returns the value `t` with the input context.
    pub fn ret<T, E>(self, t: T) -> ParseResult<'a, I, T, E> {
        internal::data(self.0, t)
    }

    /// Returns the error value `e` with the input context.
    pub fn err<T, E>(self, e: E) -> ParseResult<'a, I, T, E> {
        internal::error(self.0, e)
    }
}

/// The basic return type of a parser.
#[must_use]
#[derive(Debug, Eq, PartialEq)]
pub struct ParseResult<'a, I: 'a, T: 'a, E: 'a>(State<'a, I, T, E>);

impl<'a, I, T, E> ParseResult<'a, I, T, E> {
    pub fn bind<F, U, V = E>(self, f: F) -> ParseResult<'a, I, U, V>
      where F: FnOnce(Input<'a, I>, T) -> ParseResult<'a, I, U, V>,
            V: From<E> {
        match self.0 {
            State::Data(i, t)    => f(Input(i), t).map_err(From::from),
            State::Error(i, e)   => ParseResult(State::Error(i, From::from(e))),
            State::Incomplete(n) => ParseResult(State::Incomplete(n)),
        }
    }

    pub fn map<U, F>(self, f: F) -> ParseResult<'a, I, U, E>
      where F: FnOnce(T) -> U {
        match self.0 {
            State::Data(i, t)    => ParseResult(State::Data(i, f(t))),
            State::Error(i, e)   => ParseResult(State::Error(i, e)),
            State::Incomplete(n) => ParseResult(State::Incomplete(n)),
        }
    }

    pub fn map_err<V, F>(self, f: F) -> ParseResult<'a, I, T, V>
      where F: FnOnce(E) -> V {
        match self.0 {
            State::Data(i, t)    => ParseResult(State::Data(i, t)),
            State::Error(i, e)   => ParseResult(State::Error(i, f(e))),
            State::Incomplete(n) => ParseResult(State::Incomplete(n)),
        }
    }
}

impl<'a, I, T, E: fmt::Debug> ParseResult<'a, I, T, E> {
    /// Extracts the contained type if the parser is in a success-state, panics otherwise.
    #[inline]
    pub fn unwrap(self) -> T {
        match self.0 {
            State::Data(_, t)    => t,
            State::Error(_, e)   => panic!("called `Parser::unwrap` on a parser in an error state: {:?}", e),
            State::Incomplete(_) => panic!("called `Parser::unwrap` on a parser in an incomplete state"),
        }
    }
}

impl<'a, I, T: fmt::Debug, E> ParseResult<'a, I, T, E> {
    pub fn unwrap_err(self) -> E {
        match self.0 {
            State::Data(_, t)    => panic!("called `Parser::unwrap_err` on a parser in a success state: {:?}", t),
            State::Error(_, e)   => e,
            State::Incomplete(_) => panic!("called `Parser::unwrap_err` on a parser in an incomplete state"),
        }
    }
}

/// Result for dealing with the basic parsers when parsing a stream of `u8`.
pub type U8Result<'a, T>        = ParseResult<'a, u8, T, Error<u8>>;
/// Result returned from the basic parsers.
pub type SimpleResult<'a, I, T> = ParseResult<'a, I, T, Error<I>>;

#[cfg(feature = "verbose_error")]
mod err {
    //! This is a private module to contain the more verbose error type as well as adapters for
    //! using it.
    //! 
    //! All adapters are #[inline(always)] and will construct the appropriate error type.
    use std::any;
    use std::error;
    use std::fmt;

    use ::ParseResult;
    use ::internal;

    #[derive(Debug, Eq, PartialEq)]
    pub enum Error<I> {
        Expected(I),
        Unexpected,
        String(Vec<I>),
    }

    impl<I> fmt::Display for Error<I>
      where I: fmt::Debug {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match *self {
                Error::Expected(ref c) => write!(f, "expected {:?}", *c),
                Error::Unexpected      => write!(f, "unexpected"),
                Error::String(ref s)   => write!(f, "expected {:?}", *s),
            }
        }
    }

    impl<I> error::Error for Error<I>
      where I: any::Any + fmt::Debug {
        fn description(&self) -> &str {
            match *self {
                Error::Expected(_) => "expected a certain token, received another",
                Error::Unexpected  => "received an unexpected token",
                Error::String(_)   => "expected a certain string of tokens, encountered an unexpected token",
            }
        }
    }

    #[inline(always)]
    pub fn unexpected<I>() -> Error<I> {
        Error::Unexpected
    }

    #[inline(always)]
    pub fn expected<'a, I>(i: I) -> Error<I> {
        Error::Expected(i)
    }


    #[inline(always)]
    pub fn string<'a, 'b, I, T>(buffer: &'a [I], _offset: usize, expected: &'b [I]) -> ParseResult<'a, I, T, Error<I>>
      where I: Copy {
        internal::error(buffer, Error::String(expected.to_vec()))
    }
}

#[cfg(not(feature = "verbose_error"))]
mod err {
    //! This is a private module to contain the smaller error type as well as adapters for using
    //! it.
    //! 
    //! All adapters are #[inline(always)], and will just noop the data.
    use ::std::any;
    use ::std::error;
    use ::std::fmt;

    use ::std::marker::PhantomData;

    use ::ParseResult;
    use ::internal;

    #[derive(Debug, Eq, PartialEq)]
    pub struct Error<I>(PhantomData<I>);

    impl<I: fmt::Debug> fmt::Display for Error<I> {
        fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
            write!(f, "generic parse error (chomp was compiled without --feature verbose_error)")
        }
    }

    impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
        fn description(&self) -> &str {
            "generic parse error (chomp was compiled without --feature verbose_error)"
        }
    }

    #[inline(always)]
    pub fn unexpected<I>() -> Error<I> {
        Error(PhantomData)
    }

    #[inline(always)]
    pub fn expected<'a, I>(_: I) -> Error<I> {
        Error(PhantomData)
    }

    #[inline(always)]
    pub fn string<'a, 'b, I, T>(buffer: &'a [I], offset: usize, _expected: &'b [I]) -> ParseResult<'a, I, T, Error<I>>
      where I: Copy {
        internal::error(&buffer[offset..], Error(PhantomData))
    }
}
