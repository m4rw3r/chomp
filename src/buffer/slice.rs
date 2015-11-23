use std::marker::PhantomData;

use internal::input;
use internal::{State, ParseResultModify};

use {Input, ParseResult};
use buffer::{IntoStream, ParseError, Stream};

/// Stream implementation for slices.
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::{token, take};
/// use chomp::buffer::{IntoStream, Stream};
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
/// use chomp::{token, many, take};
/// use chomp::buffer::{IntoStream, Stream};
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
pub struct SliceStream<'a, 'i, I: 'i>(&'i [I], PhantomData<&'a u8>);

impl<'a, 'i, I: 'i> IntoStream<'a, 'i> for &'i [I] {
    type Item = I;
    type Into = SliceStream<'a, 'i, I>;

    fn into_source(self) -> SliceStream<'a, 'i, I> {
        SliceStream(self, PhantomData)
    }
}

impl<'a, 'i, I> Stream<'a, 'i, I> for SliceStream<'a, 'i, I> {
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
