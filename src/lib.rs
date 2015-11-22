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
//! Chomp's functionality is split between three modules:
//!
//! * `parsers` contains the basic parsers used to parse streams of input.
//! * `combinators` contains functions which take parsers and return new ones.
//! * `internal` contains the building blocks used to make new parsers. This is advanced usage and
//!   is far more involved than using the pre-existing parsers, but is sometimes unavoidable.
//!
//! A parser is, at its simplest, a function that takes a slice of input and returns a
//! `ParserResult<'a, I, T, E>`, where `I`, `T`, and `E` are the input, output, and error types,
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
//! satisfy(|c| {
//!     match c {
//!         b'c' | b'h' | b'a' | b'r' => true,
//!         _ => false,
//!     }
//! })
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
//! In other words, just as a normal Rust function usually looks something like this:
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
//! A Chomp parser with a similar structure looks like this:
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

#[macro_use]
extern crate bitflags;
extern crate conv;

#[macro_use]
mod macros;
mod input;
mod parse_result;

pub mod ascii;
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
    eof,
    not_token,
    peek,
    satisfy,
    scan,
    string,
    take,
    take_remainder,
    take_till,
    take_while,
    take_while1,
    token,
};
pub use err::Error;
pub use internal::iter::Iter;
pub use input::Input;
pub use parse_result::{
    U8Result,
    SimpleResult,
    ParseResult,
};

#[cfg(feature = "verbose_error")]
mod err {
    //! This is a private module to contain the more verbose error type as well as adapters for
    //! using it.
    //!
    //! All adapters are #[inline(always)] and will construct the appropriate error type.
    use std::any;
    use std::error;
    use std::fmt;

    use {Input, ParseResult};

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
    pub fn string<'a, 'b, I, T>(i: Input<'a, I>, _offset: usize, expected: &'b [I])
        -> ParseResult<'a, I, T, Error<I>>
      where I: Copy {
        i.err(Error::String(expected.to_vec()))
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

    use {Input, ParseResult};

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
    pub fn string<'a, 'b, I, T>(i: Input<'a, I>, offset: usize, _expected: &'b [I])
        -> ParseResult<'a, I, T, Error<I>>
      where I: Copy {
        use internal::InputModify;
        let b = i.buffer();

        i.replace(&b[offset..]).err(Error(PhantomData))
    }
}
