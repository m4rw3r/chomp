use primitives::input;
use primitives::{State, IntoInner};

use {InputBuf, ParseResult};
use buffer::{IntoStream, StreamError, Stream};

/// Stream implementation for immutable slices.
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::{token, take};
/// use chomp::buffer::{IntoStream, Stream};
///
/// let i = b"foo";
///
/// let r = i.into_stream().parse(parser!{
///     token(b'f');
///     take(2)
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
/// let r = i.into_stream().parse(parser!{many(parser!{
///     token(b'f');
///     take(2)
/// })});
///
/// assert_eq!(r, Ok(vec![b"oo" as &[u8], b"oo" as &[u8]]));
/// # }
/// ```
#[derive(Debug, Eq, PartialEq, Hash)]
pub struct SliceStream<'i, I: 'i> {
    pos:   usize,
    slice: &'i [I],
}

impl<'i, I: 'i> SliceStream<'i, I> {
    /// Creates a new stream from an immutable slice.
    #[inline]
    pub fn new(slice: &'i [I]) -> Self {
        SliceStream {
            pos:   0,
            slice: slice,
        }
    }

    /// The number of bytes left in the buffer
    #[inline]
    pub fn len(&self) -> usize {
        self.slice.len() - self.pos
    }

    /// Returns true if no more bytes are available
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, 'i, I: 'i + Copy> IntoStream<'a, 'i> for &'i [I] {
    type Item = I;
    type Into = SliceStream<'i, I>;

    #[inline]
    fn into_stream(self) -> SliceStream<'i, I> {
        SliceStream::new(self)
    }
}

impl<'a, 'i, I: 'i + Copy> Stream<'a, 'i> for SliceStream<'i, I> {
    type Item = I;

    #[inline]
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, StreamError<'i, Self::Item, E>>
      where F: FnOnce(InputBuf<'i, Self::Item>) -> ParseResult<InputBuf<'i, Self::Item>, T, E>,
            T: 'i,
            E: 'i {
        use primitives::Primitives;

        if self.is_empty() {
            return Err(StreamError::EndOfInput);
        }

        match f(input::new_buf(input::END_OF_INPUT, &self.slice[self.pos..])).into_inner() {
            State::Data(remainder, data) => {
                // TODO: Do something neater with the remainder
                self.pos += self.len() - remainder.min_remaining();

                Ok(data)
            },
            State::Error(mut remainder, err) => {
                // TODO: Do something neater with the remainder
                // TODO: Detail this behaviour, maybe make it configurable
                let r = remainder.min_remaining();

                self.pos += self.len() - r;

                Err(StreamError::ParseError(remainder.consume(r), err))
            },
            State::Incomplete(_, n) => Err(StreamError::Incomplete(n + self.len())),
        }
    }
}
