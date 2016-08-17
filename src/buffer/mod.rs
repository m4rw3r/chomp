//! Utilities for parsing streams of data.
//!
//! # Examples
//!
//! ```
//! # #[macro_use] extern crate chomp;
//! # fn main() {
//! use std::fs::File;
//!
//! use chomp::buffer;
//! use chomp::buffer::Stream;
//! use chomp::prelude::{token, take_while, take_while1};
//! use chomp::ascii::is_whitespace;
//!
//! let f = File::open("./README.md").unwrap();
//!
//! let mut b = buffer::Source::from_read(f, buffer::FixedSizeBuffer::new());
//!
//! let r = b.parse(parser!{
//!     take_while(|c| c != b'#');
//!     token(b'#');
//!     take_while1(is_whitespace);
//!     take_while1(|c| c != b'\r' && c != b'\n')
//! });
//!
//! assert_eq!(r, Ok(&b"Chomp"[..]));
//! # }
//! ```

mod stateful;
mod buffer;
mod slice;

pub mod data_source;

use std::io;

use types::{Input, ParseResult};
use types::Buffer as InputBuffer;
use primitives::Guard;

pub use self::slice::SliceStream;
pub use self::data_source::DataSource;
pub use self::stateful::Source;
pub use self::buffer::{
    Buffer,
    FixedSizeBuffer,
    GrowingBuffer,
};

/// Error type for parsing using the `Stream` trait.
#[derive(Debug)]
pub enum StreamError<B: InputBuffer, E> {
    /// An error occurred in the parser, the given slice indicates the part which failed.
    ParseError(B, E),
    /// Parser failed to complete with the available data.
    Incomplete,
    /// An IO-error occurred while attempting to fill the buffer.
    IoError(io::Error),
    /// The last parser completed successfully and there is no more input to parse.
    EndOfInput,
    /// The last parser failed with an incomplete state, fill the buffer and try again.
    ///
    /// Filling the buffer is automatic by default.
    Retry,
}

impl<B: InputBuffer, E: PartialEq<E>> PartialEq for StreamError<B, E> {
    #[inline]
    fn eq(&self, other: &StreamError<B, E>) -> bool {
        match (self, other) {
            (&StreamError::ParseError(ref b1, ref e1), &StreamError::ParseError(ref b2, ref e2)) => b1 == b2 && e1 == e2,
            (&StreamError::Incomplete, &StreamError::Incomplete)
              | (&StreamError::EndOfInput, &StreamError::EndOfInput)
              | (&StreamError::Retry, &StreamError::Retry)           => true,
            _ => false,
        }
    }
}

/// Trait wrapping the state management in reading from a data source while parsing.
pub trait Stream<'a, 'i> {
    /// The input item type, usually depending on which `DataSource` is used.
    type Item: 'i + Copy + PartialEq;

    /// Attempts to run the supplied parser `F` once on the currently populated data in this
    /// stream, providing a borrow of the inner data storage.
    ///
    /// If a `StreamError::Retry` is returned the consuming code it should just retry the action
    /// (the implementation might require a separate call to refill the stream).
    #[inline]
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, StreamError<&'i [Self::Item], E>>
      where F: FnOnce(InputBuf<'i, Self::Item>) -> ParseResult<InputBuf<'i, Self::Item>, T, E>,
            T: 'i,
            E: 'i;
}

/// Trait for conversion into a `Stream`.
pub trait IntoStream<'a, 'i> {
    /// The input item type provided by the stream.
    type Item: 'i + Copy + PartialEq;
    /// The `Stream` instance type.
    type Into: Stream<'a, 'i, Item=Self::Item>;

    /// Convert self into a `Stream`.
    #[inline]
    fn into_stream(self) -> Self::Into;
}

// FIXME: Docs
/// Input buffer type which contains a flag which tells if we might need to read more data.
#[must_use]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InputBuf<'a, I: 'a>(
    /// If this is set to true a parser has tried to read past the end of this buffer.
    pub bool,
    /// Current buffer slice
    pub &'a [I],
);

// FIXME: Docs
impl<'a, I: 'a> InputBuf<'a, I> {
    #[inline]
    pub fn new(buf: &'a [I]) -> Self {
        InputBuf(false, buf)
    }

    #[inline]
    pub fn is_incomplete(&self) -> bool {
        self.0
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.1.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, I: Copy + PartialEq> Input for InputBuf<'a, I> {
    type Token  = I;
    type Marker = &'a [I];
    type Buffer = &'a [I];

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        if let Some(c) = self.1.first() {
            Some(*c)
        } else {
            self.0 = true;

            None
        }
    }

    #[inline]
    fn _pop(&mut self, g: Guard) -> Option<Self::Token> {
        self._peek(g).map(|c| {
            self.1 = &self.1[1..];

            c
        })
    }

    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        if n > self.1.len() {
            self.0 = true;

            None
        } else {
            let b = &self.1[..n];

            self.1 = &self.1[n..];

            Some(b)
        }
    }

    #[inline]
    fn _consume_while<F>(&mut self, g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        if let Some(n) = self.1.iter().position(|c| !f(*c)) {
            let b = &self.1[..n];

            self.1 = &self.1[n..];

            b
        } else {
            self._consume_remaining(g)
        }
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        &m[..m.len() - self.1.len()]
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        self.0 = true;

        let b = self.1;

        self.1 = &self.1[..0];

        b
    }

    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        // Incomplete state is separate from the parsed state, no matter how we hit incomplete we
        // want to keep it.
        &self.1
    }

    #[inline]
    fn _restore(mut self, _g: Guard, m: Self::Marker) -> Self {
        self.1 = m;

        self
    }
}

#[cfg(test)]
mod test {
    use super::InputBuf;
    use types::{Input, ParseResult};
    use primitives::{IntoInner, Primitives};

    use types::test::run_primitives_test;

    #[test]
    fn ret() {
        let i1: InputBuf<u8> = InputBuf::new(b"in1");
        let i2: InputBuf<u8> = InputBuf::new(b"in2");

        let r1: ParseResult<_, u32, ()> = i1.ret::<_, ()>(23u32);
        let r2: ParseResult<_, i32, &str> = i2.ret::<_, &str>(23i32);

        assert_eq!(r1.into_inner(), (InputBuf::new(b"in1"), Ok(23u32)));
        assert_eq!(r2.into_inner(), (InputBuf::new(b"in2"), Ok(23i32)));
    }

    #[test]
    fn err() {
        let i1: InputBuf<u8> = InputBuf::new(b"in1");
        let i2: InputBuf<u8> = InputBuf::new(b"in2");

        let r1: ParseResult<_, (), u32>   = i1.err::<(), _>(23u32);
        let r2: ParseResult<_, &str, i32> = i2.err::<&str, _>(23i32);

        assert_eq!(r1.into_inner(), (InputBuf::new(b"in1"), Err(23u32)));
        assert_eq!(r2.into_inner(), (InputBuf::new(b"in2"), Err(23i32)));
    }

    #[test]
    fn test_input_buf() {

        run_primitives_test(InputBuf::new(b"abc"), |x| x);

        let mut b = InputBuf::new(b"a");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        b.peek();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        b.pop();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.peek(), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.pop(), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);
        b.consume(1);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        b.consume(1);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.consume(1), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.consume(3), None);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 2);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.consume_while(|_| true), &b"ab"[..]);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"ab");
        assert_eq!(b.consume_while(|c| c == b'a'), &b"a"[..]);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.consume_while(|c| c == b'b'), &b"b"[..]);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.consume_while(|c| c == b'b'), &b""[..]);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"abc");
        let m = b.mark();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);
        b.consume(3);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
        assert_eq!(b.consume_from(m), &b"abc"[..]);
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);

        let mut b = InputBuf::new(b"abc");
        let m = b.mark();
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);
        b.consume(2);
        b.consume(2);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 1);
        assert_eq!(b.is_empty(), false);
        let b = b.restore(m);
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);

        let mut b = InputBuf::new(b"abc");
        assert_eq!(b.is_incomplete(), false);
        assert_eq!(b.len(), 3);
        assert_eq!(b.is_empty(), false);
        b.consume_remaining();
        assert_eq!(b.is_incomplete(), true);
        assert_eq!(b.len(), 0);
        assert_eq!(b.is_empty(), true);
    }
}
