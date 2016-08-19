use types::{Input, Parser};
use buffer::{InputBuf, StreamError, Stream};

/// Stream implementation for immutable slices.
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::parsers::{token, take};
/// use chomp::buffer::{SliceStream, Stream};
///
/// let r = SliceStream::new(b"foo").parse(parser!{
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
/// use chomp::prelude::{token, many, take};
/// use chomp::buffer::{SliceStream, Stream};
///
/// let r = SliceStream::new(b"foofoo").parse(parser!{many(parser!{
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

impl<'a, 'i, I: 'i + Copy + PartialEq> Stream<'a, 'i> for SliceStream<'i, I> {
    type Input = InputBuf<'i, I>;

    #[inline]
    fn parse<P>(&'a mut self, p: P) -> Result<P::Output, StreamError<<Self::Input as Input>::Buffer, P::Error>>
      where P: Parser<Self::Input> {
        if self.is_empty() {
            return Err(StreamError::EndOfInput);
        }

        match p.parse(InputBuf::new(&self.slice[self.pos..])) {
            (remainder, Ok(data)) => {
                // TODO: Do something neater with the remainder
                self.pos += self.len() - remainder.len();

                Ok(data)
            },
            (mut remainder, Err(err)) => {
                if remainder.is_incomplete() {
                    Err(StreamError::Incomplete)
                } else {
                    // TODO: Do something neater with the remainder
                    // TODO: Detail this behaviour, maybe make it configurable
                    let r = remainder.len();

                    self.pos += self.len() - r;

                    Err(StreamError::ParseError(remainder.consume_remaining(), err))
                }
            },
        }
    }
}
