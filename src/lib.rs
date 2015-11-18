//! Chomp is an alternative parser combinator library for the Rust programming language. It was
//! written as the culmination of the experiments detailed in these blog posts:
//!
//! * [Part 1](http://m4rw3r.github.io/parser-combinator-experiments-rust/)
//! * [Part 2](http://m4rw3r.github.io/parser-combinator-experiments-errors)
//! * [Part 3](http://m4rw3r.github.io/parser-combinator-experiments-part-3)
//!
//! For its current capabilities, you will find that Chomp performs consistently as well, if not
//! better, than optimized C parsers, while being vastly more expressive. For an example that
//! builds a performant HTTP parser out of smaller parsers, see
//! [http_parser.rs](examples/http_parser.rs).
//!
//! # Example
//!
//! ```
//! # #[macro_use] extern crate chomp;
//! # fn main() {
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
//!     parse!{i;
//!         let first = take_while1(|c| c != b' ');
//!                     token(b' ');  // skipping this char
//!         let last  = take_while1(|c| c != b'\n');
//!
//!         ret Name{
//!             first: first,
//!             last:  last,
//!         }
//!     }
//! }
//!
//! assert_eq!(name(i).unwrap(), Name{first: b"martin", last: "wernstål".as_bytes()});
//! # }
//! ```
//!
//! # Usage
//!
//! Chomp's functionality is split between three modules.
//!
//! * `parsers` contains the basic parsers used to parse streams of input.
//! * `combinators` contains functions which take parsers and return new ones.
//! * `internal` contains the building blocks used to make new parsers. This is advanced usage and
//!   is far more involved than using the pre-existing parsers, but is sometimes unavoidable.
//!
//! A parser is, at its simplest, a function that takes a slice of input and returns a
//! `ParserResult<'a, I, T, E>`, where I, T, and E are the input, output, and error types,
//! respectively. Parsers are usually parameterized over values or other parsers as well, so these
//! appear as extra arguments in the parsing function. As an example, here is the signature of the
//! `token` parser, which matches a particular input.
//!
//! ```ignore
//! fn token<'a, I: 'a + Copy + Eq>(i: Input<'a, I>, t: I) -> SimpleResult<'a, I, I> {...}
//! ```
//!
//! Notice that the first argument is an `Input<'a, I>`, and the second argument is some `I`.
//! `Input<'a,I>` is just a datatype over the current state of the parser and a slice of input `I`,
//! and prevents the parser writer from accidentally mutating the state of the parser. Later, when
//! we introduce the `parse!` macro, we will see that using a parser in this macro just means
//! supplying all of the arguments but the input, as so:
//!
//! ```ignore
//! token(b'T');
//! ```
//!
//! Note that you cannot do this outside of the `parse!` macro. `SimpleResult<'a, I, T>` is a
//! convenience type alias over `Result<'a, I, T, Error<u8>>`, and `Error<I>` is just a convenient
//! "default" error type that will be sufficient for most uses. For more sophisticated usage, one
//! can always write a custom error type.
//!
//! A very useful parser is the `satisfy` parser:
//!
//! ```ignore
//! fn satisfy<'a, I: 'a + Copy, F>(i: Input<'a, I>, f: F) -> SimpleResult<'a, I, I>
//!    where F: FnOnce(I) -> bool { ... }
//! ```
//!
//! Besides the input state, satisfy's only parameter is a predicate function and will succeed only
//! if the next piece of input satisfies the supplied predicate. Here's an example that might be
//! used in the `parse!` macro:
//!
//! ```
//! # #[macro_use] extern crate chomp;
//! # fn main() {
//! # use chomp::{Input, satisfy};
//! # let r = parse!{Input::new(b"h");
//!    satisfy(|c| {
//!        match c {
//!            b'c' | b'h' | b'a' | b'r' => true,
//!            _ => false,
//!        }
//!    })
//! # };
//! # assert_eq!(r.unwrap(), b'h');
//! # }
//! ```
//!
//! This parser will only succeed if the character is one of the characters in "char".
//!
//! Lastly, here is the parser combinator `count`, which will attempt to run a parser a number of
//! times on its input.
//!
//! ```ignore
//! pub fn count<'a, I, T, E, F, U>(i: Input<'a, I>, num: usize, p: F) -> ParseResult<'a, I, T, E>
//!   where I: Copy,
//!         U: 'a,
//!         F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
//!         T: FromIterator<U> { ... }
//! ```
//!
//! Using parsers is almost entirely done using the `parse!` macro, which enables us to do three
//! distinct things:
//!
//! * Sequence parsers over the remaining input
//! * Store intermediate results into datatypes
//! * Return a datatype at the end, which may be the result of any arbitrary computation over the
//! intermediate results.
//!
//! In other words, just as a normal Rust function usually looks something like
//!
//! ```
//! # fn launch_missiles() {}
//! fn f() -> (u8, u8, u8) {
//!     let a = 3;
//!     let b = 3;
//!     launch_missiles();
//!     return (a, b, a + b);
//! }
//! ```
//!
//! A Chomp parser looks something like
//!
//! ```
//! # #[macro_use] extern crate chomp;
//! # use chomp::{Input, string, token, U8Result};
//! fn f(i: Input<u8>) -> U8Result<(u8, u8, u8)> {
//!     parse!{i;
//!         let a = token(b'3');
//!         let b = token(b'3');
//!         string(b"missiles");
//!         ret (a, b, a + b)
//!     }
//! }
//! # fn main() {
//! #     let r = f(Input::new(b"33missiles"));
//! #     assert_eq!(r.unwrap(), (b'3', b'3', b'f')); // b'3' + b'3' == b'f'
//! # }
//! ```
//!
//! Readers familiar with Haskell or F# will recognize this as a "monadic computation" or
//! "computation expression".
//!
//! You use the `parse!` macro as follows:
//!
//! - Write the input parameter first, with a semicolon.
//! - Write any number of valid parser actions or identifier bindings, where:
//!    - a parser action takes the form `parser(params*)`, with the input parameter omitted.
//!    - an identifier binding takes the form `let identifer = parser(params*);`, with the input
//!      parameter omitted.
//! - Write the final line of the macro, which must always be either a parser action, or a return
//!   statement which takes the form `ret expression`. The type of `expression` becomes the return
//!   type of the entire parser, should it succeed.
//!
//! The entire grammar for the macro is listed elsewhere in this documentation.

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
    #[inline]
    pub fn new(i: &'a [I]) -> Self {
        Input(i)
    }

    /// Returns the value `t` with the input context.
    #[inline]
    pub fn ret<T, E>(self, t: T) -> ParseResult<'a, I, T, E> {
        internal::data(self.0, t)
    }

    /// Returns the error value `e` with the input context.
    #[inline]
    pub fn err<T, E>(self, e: E) -> ParseResult<'a, I, T, E> {
        internal::error(self.0, e)
    }
}

/// The basic return type of a parser.
///
/// This type satisfies a variant of the ``Monad`` typeclass. Due to the limitations of Rust's
/// return types closures cannot be returned without boxing which has an unacceptable performance
/// impact.
///
/// To get around this issue and still provide a simple to use and safe (as in hard to accidentally
/// violate the monad laws or the assumptions taken by the parser type) an `Input` wrapper is
/// provided which ensures that the parser state is carried properly through every call to `bind`.
/// This is also known as a Linear Type (emulated through hiding destructors and using the
/// annotation ``#[must_use]``).
///
/// Do-notation is provided by the macro ``parse!``.
///
/// # Equivalence with Haskell's ``Monad`` typeclass:
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
pub struct ParseResult<'a, I: 'a, T: 'a, E: 'a>(State<'a, I, T, E>);

impl<'a, I, T, E> ParseResult<'a, I, T, E> {
    /// Sequentially composes the result with a parse action ``f``, passing any produced value as
    /// the second parameter.
    ///
    /// The first parameter to the supplied function ``f`` is the parser state (``Input``). This
    /// state is then passed on to other parsers or used to return a value or an error.
    ///
    /// # Automatic conversion of ``E``
    ///
    /// The error value ``E`` will automatically be converted using the ``From`` trait to the
    /// desired type. The downside with this using the current stable version of Rust (1.4) is that
    /// the type inferrence will currently not use the default value for the generic ``V`` and will
    /// therefore require extra type hint for the error.
    ///
    /// # Examples
    ///
    /// ```
    /// use chomp::{Input, Error};
    ///
    /// let p = Input::new(b"test").ret("data".to_owned());
    /// // Explicitly state the error type
    /// let r = p.bind::<_, _, ()>(|i, x| i.ret(x + " here!"));
    ///
    /// assert_eq!(r.unwrap(), "data here!");
    /// ```
    ///
    /// Using a function which wraps the expression will both make it easier to compose and also
    /// provides the type-hint for the error in the function signature:
    ///
    /// ```
    /// use chomp::{Input, ParseResult};
    ///
    /// fn parser(i: Input<u8>, n: i32) -> ParseResult<u8, i32, ()> {
    ///     i.ret(n + 10)
    /// }
    ///
    /// let p = Input::new(b"test").ret(23);
    ///
    /// assert_eq!(p.bind(parser).unwrap(), 33);
    /// ```
    #[inline]
    pub fn bind<F, U, V = E>(self, f: F) -> ParseResult<'a, I, U, V>
      where F: FnOnce(Input<'a, I>, T) -> ParseResult<'a, I, U, V>,
            V: From<E> {
        match self.0 {
            State::Data(i, t)    => f(Input(i), t).map_err(From::from),
            State::Error(i, e)   => ParseResult(State::Error(i, From::from(e))),
            State::Incomplete(n) => ParseResult(State::Incomplete(n)),
        }
    }

    /// Sequentially composes the result with a parse action ``f``, discarding any produced value.
    ///
    /// The first parameter to the supplied function ``f`` is the parser state (``Input``). This
    /// state is then passed on to other parsers or used to return a value or an error.
    ///
    /// # Relation to ``bind``
    ///
    /// ```text
    /// ParseResult::then(g)  ≡  ParseResult::bind(|i, _| g(i))
    /// ```
    ///
    /// # Example
    ///
    /// ```
    /// use chomp::{Input, U8Result};
    ///
    /// fn g(i: Input<u8>) -> U8Result<&'static str> {
    ///     i.ret("testing!")
    /// }
    ///
    /// let p1 = Input::new(b"data").ret("initial state");
    /// let p2 = Input::new(b"data").ret("initial state");
    ///
    /// assert_eq!(p1.bind(|i, _| g(i)).unwrap(), "testing!");
    /// assert_eq!(p2.then(g).unwrap(), "testing!");
    /// ```
    #[inline]
    pub fn then<F, U, V = E>(self, f: F) -> ParseResult<'a, I, U, V>
      where F: FnOnce(Input<'a, I>) -> ParseResult<'a, I, U, V>,
            V: From<E> {
        self.bind(|i, _| f(i))
    }

    #[inline]
    pub fn map<U, F>(self, f: F) -> ParseResult<'a, I, U, E>
      where F: FnOnce(T) -> U {
        match self.0 {
            State::Data(i, t)    => ParseResult(State::Data(i, f(t))),
            State::Error(i, e)   => ParseResult(State::Error(i, e)),
            State::Incomplete(n) => ParseResult(State::Incomplete(n)),
        }
    }

    #[inline]
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
    /// Unwraps a parse result, yielding the content of the success-state.
    ///
    /// # Panics
    ///
    /// Panics if the parse result is in an error-state or if the parsing is incomplete. Will
    /// provide a panic message based on the value of the error.
    ///
    /// # Examples
    ///
    /// ```
    /// use chomp::{Input, token};
    ///
    /// let r = token(Input::new(b"a"), b'a');
    ///
    /// assert_eq!(r.unwrap(), b'a');
    /// ```
    ///
    /// ```{.should_panic}
    /// use chomp::{Input, token};
    ///
    /// let r = token(Input::new(b"a"), b'b');
    ///
    /// // Panics with "called `ParseResult::unwrap` on an error: Expected (98)"
    /// assert_eq!(r.unwrap(), b'a');
    /// ```
    ///
    /// ```{.should_panic}
    /// use chomp::{Input, take_while};
    ///
    /// let r = take_while(Input::new(b"a"), |c| c == b'a');
    ///
    /// // Panics with "called `ParseResult::unwrap` on an incomplete state (requested 1 tokens)"
    /// assert_eq!(r.unwrap(), b"a");
    /// ```
    #[inline]
    pub fn unwrap(self) -> T {
        match self.0 {
            State::Data(_, t)    => t,
            State::Error(_, e)   => panic!("called `ParseResult::unwrap` on an error: {:?}", e),
            State::Incomplete(n) => panic!(
                "called `ParseResult::unwrap` on an incomplete state (requested {} tokens)",
                n),
        }
    }

    /// Unwraps a parse result, yielding the contents of the success state.
    ///
    /// # Panics
    ///
    /// Panics if the parse result is in an error-state or if the parsing is incomplete. Will
    /// provide a panic message based on the supplied message and the value of the error.
    ///
    /// # Examples
    ///
    /// ```{.should_panic}
    /// use chomp::{Input, token};
    ///
    /// let r = token(Input::new(b"a"), b'b');
    ///
    /// // Panics with "Wanted character b: Expected(98)"
    /// assert_eq!(r.expect("Wanted character b"), b'a');
    /// ```
    #[inline]
    pub fn expect(self, msg: &str) -> T {
        match self.0 {
            State::Data(_, t)    => t,
            State::Error(_, e)   => panic!("{}: {:?}", msg, e),
            State::Incomplete(_) => panic!("{}: Parser in an incomplete state", msg),
        }
    }
}

impl<'a, I, T: fmt::Debug, E> ParseResult<'a, I, T, E> {
    /// Unwraps a parse result, yielding the contents of the error state.
    ///
    /// # Panics
    ///
    /// Panics if the parse result is in a success-state or if the parsing is incomplete. Will
    /// provide a panic message based on the value of the success or incomplete state.
    ///
    /// # Examples
    ///
    /// ```
    /// use chomp::{Error, Input, token};
    ///
    /// let r = token(Input::new(b"a"), b'b');
    ///
    /// assert_eq!(r.unwrap_err(), Error::Expected(98));
    /// ```
    ///
    /// ```{.should_panic}
    /// use chomp::{Error, Input, token};
    ///
    /// let r = token(Input::new(b"a"), b'a');
    ///
    /// // Panics with "called `ParseResult::unwrap_err` on a success state: 97"
    /// assert_eq!(r.unwrap_err(), Error::Expected(98));
    /// ```
    #[inline]
    pub fn unwrap_err(self) -> E {
        match self.0 {
            State::Data(_, t)    => panic!(
                "called `ParseResult::unwrap_err` on a success state: {:?}",
                t),
            State::Error(_, e)   => e,
            State::Incomplete(n) => panic!(
                "called `ParseResult::unwrap_err` on an incomplete state (requested {} tokens)",
                n),
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

    use ParseResult;
    use internal::error;

    #[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
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

    impl<I: any::Any + fmt::Debug> error::Error for Error<I> {
        fn description(&self) -> &str {
            match *self {
                Error::Expected(_) => "expected a certain token, received another",
                Error::Unexpected  => "received an unexpected token",
                Error::String(_)   =>
                    "expected a certain string of tokens, encountered an unexpected token",
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
    pub fn string<'a, 'b, I, T>(buffer: &'a [I], _offset: usize, expected: &'b [I])
        -> ParseResult<'a, I, T, Error<I>>
      where I: Copy {
        error(buffer, Error::String(expected.to_vec()))
    }
}

#[cfg(not(feature = "verbose_error"))]
mod err {
    //! This is a private module to contain the smaller error type as well as adapters for using
    //! it.
    //!
    //! All adapters are #[inline(always)], and will just noop the data.
    use std::any;
    use std::error;
    use std::fmt;

    use std::marker::PhantomData;

    use ParseResult;
    use internal::error;

    #[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
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
    pub fn string<'a, 'b, I, T>(buffer: &'a [I], offset: usize, _expected: &'b [I])
        -> ParseResult<'a, I, T, Error<I>>
      where I: Copy {
        error(&buffer[offset..], Error(PhantomData))
    }
}

#[cfg(test)]
mod test {
    use {Input, ParseResult};
    use internal::State;

    #[test]
    fn monad_left_identity() {
        fn f<I: Copy>(i: Input<I>, n: u32) -> ParseResult<I, u32, ()> {
            i.ret(n + 1)
        }

        let m1 = Input(b"test");
        let m2 = Input(b"test");

        let a = 123;
        // return a >>= f
        let lhs = m1.ret(a).bind(f);
        // f a
        let rhs = f(m2, a);

        assert_eq!(lhs.0, State::Data(b"test", 124));
        assert_eq!(rhs.0, State::Data(b"test", 124));
    }

    #[test]
    fn monad_right_identity() {
        let m1 = Input(b"test").ret::<_, ()>(1);
        let m2 = Input(b"test").ret::<_, ()>(1);

        // m1 >>= ret === m2
        let lhs = m1.bind::<_, _, ()>(Input::ret);
        let rhs = m2;

        assert_eq!(lhs.0, State::Data(b"test", 1));
        assert_eq!(rhs.0, State::Data(b"test", 1));
    }

    #[test]
    fn monad_associativity() {
         fn f<I: Copy>(i: Input<I>, num: u32) -> ParseResult<I, u64, ()> {
            i.ret((num + 1) as u64)
        }

        fn g<I: Copy>(i: Input<I>, num: u64) -> ParseResult<I, u64, ()> {
            i.ret(num * 2)
        }

        let lhs_m = Input(b"test").ret::<_, ()>(2);
        let rhs_m = Input(b"test").ret::<_, ()>(2);

        // (m >>= f) >>= g
        let lhs = lhs_m.bind(f).bind(g);
        // m >>= (\x -> f x >>= g)
        let rhs = rhs_m.bind(|i, x| f(i, x).bind(g));

        assert_eq!(lhs.0, State::Data(b"test", 6));
        assert_eq!(rhs.0, State::Data(b"test", 6));
    }
}
