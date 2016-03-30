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

use types::{ParseResult, InputBuf};
use types::Buffer as InputBuffer;

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
            (&StreamError::Incomplete, &StreamError::Incomplete) => true,
            (&StreamError::EndOfInput, &StreamError::EndOfInput) => true,
            (&StreamError::Retry, &StreamError::Retry) => true,
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
