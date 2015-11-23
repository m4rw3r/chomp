mod stateful;
mod buffer;
mod slice;
mod data_source;

use std::io;

use {ParseResult, Input};

pub use self::slice::SliceSource;
pub use self::data_source::{
    DataSource,
    IteratorDataSource,
    ReadDataSource,
};
pub use self::stateful::{
    StatefulSource,
};
pub use self::buffer::{
    Buffer,
    FixedSizeBuffer,
    GrowingBuffer,
};

/// Error type for parsing using the `Source` trait.
#[derive(Debug)]
pub enum ParseError<'a, I, E>
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
