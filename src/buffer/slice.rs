use std::marker::PhantomData;

use internal::input;
use internal::{State, ParseResultModify};

use {Input, IntoSource, Source, ParseResult, ParseError};

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

impl<'a, 'i, I: 'i> IntoSource<'a, 'i> for &'i [I] {
    type Item = I;
    type Into = SliceSource<'a, 'i, I>;

    fn into_source(self) -> SliceSource<'a, 'i, I> {
        SliceSource(self, PhantomData)
    }
}

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
