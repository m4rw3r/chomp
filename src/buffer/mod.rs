mod read;
mod buffer;

use std::io;

use std::marker::PhantomData;

use {ParseResult, Input};
use internal::input;
use internal::{State, ParseResultModify};

pub use self::read::ReadSource;
pub use self::buffer::Buffer;
pub use self::buffer::FixedSizeBuffer;
pub use self::buffer::GrowingBuffer;

#[derive(Debug)]
pub enum ParseError<'a, I, E>
  where I: 'a {
    ParseError(&'a [I], E),
    Incomplete(usize),
    IoError(io::Error),
    EndOfInput,
    Retry,
}

impl<'a, I, E> PartialEq for ParseError<'a, I, E>
  where E: PartialEq, I: PartialEq {
    fn eq(&self, other: &ParseError<'a, I, E>) -> bool {
        match (self, other) {
            (&ParseError::ParseError(ref b1, ref e1), &ParseError::ParseError(ref b2, ref e2)) => b1 == b2 && e1 == e2,
            (&ParseError::Incomplete(n1), &ParseError::Incomplete(n2)) => n1 == n2,
            (&ParseError::EndOfInput, &ParseError::EndOfInput) => true,
            (&ParseError::Retry, &ParseError::Retry) => true,
            _ => false,
        }
    }
}

/// Trait wrapping the state management in reading from a data source while parsing.
pub trait Source<'a, 'i, I> {
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, ParseError<'i, I, E>>
      where F: FnOnce(Input<'i, I>) -> ParseResult<'i, I, T, E>,
            T: 'i,
            E: 'i;
}

/// Trait for conversion into a `Source`.
pub trait IntoSource<'a, 'i> {
    type Item;
    type Into: Source<'a, 'i, Self::Item>;

    fn into_source(self) -> Self::Into;
}

impl<'a, 'i, I: 'i> IntoSource<'a, 'i> for &'i [I] {
    type Item = I;
    type Into = SliceSource<'a, 'i, I>;

    fn into_source(self) -> SliceSource<'a, 'i, I> {
        SliceSource(self, PhantomData)
    }
}

/// Source implementation for slices.
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::{IntoSource, Source, token, take};
///
/// let i = b"foo";
///
/// let r = i.into_source().parse(parser!{
///     token(b'f');
///     take(2);
/// });
///
/// assert_eq!(r, Ok(b"oo" as &[u8]));
/// # }
/// ```
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::{IntoSource, Source, token, many, take};
///
/// let i = b"foofoo";
///
/// let r = i.into_source().parse(parser!{many(parser!{
///     token(b'f');
///     take(2);
/// })});
///
/// assert_eq!(r, Ok(vec![b"oo" as &[u8], b"oo" as &[u8]]));
/// # }
/// ```
#[derive(Debug, Eq, PartialEq, Hash)]
pub struct SliceSource<'a, 'i, I: 'i>(&'i [I], PhantomData<&'a u8>);

impl<'a, 'i, I> Source<'a, 'i, I> for SliceSource<'a, 'i, I> {
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, ParseError<'i, I, E>>
      where F: FnOnce(Input<'i, I>) -> ParseResult<'i, I, T, E>,
            T: 'i,
            E: 'i {
        match f(input::new(input::END_OF_INPUT, self.0)).internal() {
            State::Data(_, t)    => Ok(t),
            State::Error(b, e)   => Err(ParseError::ParseError(b, e)),
            State::Incomplete(n) => Err(ParseError::Incomplete(n)),
        }
    }
}

#[macro_export]
macro_rules! source_for_each {
    ( $parser:expr; $value:ident in $source:expr; $body:expr ) => {
        {
            let ref mut s = &mut $source;
            loop {
                match s.parse($parser) {
                    Ok($value) => $body,
                    Err(ParseError::Retry)      => {},
                    Err(ParseError::EndOfInput) => break,
                    Err(e)                      => { println!("{:?}", e); break; },
                }
            }
        }
    }
}
