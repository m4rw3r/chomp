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
//! use chomp::{token, take_while, take_while1};
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

use {ParseResult, Input};

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
pub enum StreamError<'a, I, E>
  where I: 'a {
    /// An error occurred in the parser, the given slice indicates the part which failed.
    ParseError(&'a [I], E),
    /// Parser failed to complete with the available data.
    Incomplete(usize),
    /// An IO-error occurred while attempting to fill the buffer.
    IoError(io::Error),
    /// The last parser completed successfully and there is no more input to parse.
    EndOfInput,
    /// The last parser failed with an incomplete state, fill the buffer and try again.
    ///
    /// Filling the buffer is automatic by default.
    Retry,
}

impl<'a, I, E> PartialEq for StreamError<'a, I, E>
  where E: PartialEq, I: PartialEq {
    #[inline]
    fn eq(&self, other: &StreamError<'a, I, E>) -> bool {
        match (self, other) {
            (&StreamError::ParseError(ref b1, ref e1), &StreamError::ParseError(ref b2, ref e2)) => b1 == b2 && e1 == e2,
            (&StreamError::Incomplete(n1), &StreamError::Incomplete(n2)) => n1 == n2,
            (&StreamError::EndOfInput, &StreamError::EndOfInput) => true,
            (&StreamError::Retry, &StreamError::Retry) => true,
            _ => false,
        }
    }
}

/// Trait wrapping the state management in reading from a data source while parsing.
pub trait Stream<'a, 'i> {
    /// The input item type, usually depending on which `DataSource` is used.
    type Item: 'i;

    /// Attempts to run the supplied parser `F` once on the currently populated data in this
    /// stream, providing a borrow of the inner data storage.
    ///
    /// If a `StreamError::Retry` is returned the consuming code it should just retry the action
    /// (the implementation might require a separate call to refill the stream).
    #[inline]
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, StreamError<'i, Self::Item, E>>
      where F: FnOnce(Input<'i, Self::Item>) -> ParseResult<'i, Self::Item, T, E>,
            T: 'i,
            E: 'i;
}

/// Trait for conversion into a `Stream`.
pub trait IntoStream<'a, 'i> {
    /// The input item type provided by the stream.
    type Item: 'i;
    /// The `Stream` instance type.
    type Into: Stream<'a, 'i, Item=Self::Item>;

    /// Convert self into a `Stream`.
    #[inline]
    fn into_stream(self) -> Self::Into;
}
