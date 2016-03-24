use std::io;
use std::cmp;

use {InputBuf, ParseResult};
use primitives::input;
use primitives::{State, IntoInner};

use buffer::{
    Buffer,
    DataSource,
    FixedSizeBuffer,
    StreamError,
    Stream,
};
use buffer::data_source::{IteratorDataSource, ReadDataSource};

bitflags!{
    flags ParserState: u64 {
        /// The parser which was last run on the buffer did not manage to complete with the data
        /// available in the buffer.
        const INCOMPLETE     = 1,
        /// The buffer did not manage to read any more data from the underlying `Read`
        /// implementation.
        const END_OF_INPUT   = 2,
        /// `parse()` should attempt to read more data whenever the `INCOMPLETE` flag is set.
        const AUTOMATIC_FILL = 4,
    }
}

/// Manages a buffer and data source pair, enabling efficient parsing from a streaming source.
#[derive(Debug)]
pub struct Source<S: DataSource, B: Buffer<S::Item>> {
    /// Source reader
    source:  S,
    /// Temporary source
    buffer:  B,
    /// The requested amount of bytes to be available for reading from the buffer
    request: usize,
    /// Input state, if end has been reached
    state:   ParserState,
}

impl<R: io::Read> Source<ReadDataSource<R>, FixedSizeBuffer<u8>> {
    /// Creates a new `Source` from a `Read` instance with the default `FixedSizeBuffer` settings.
    #[inline]
    pub fn new(source: R) -> Self {
        Self::with_buffer(ReadDataSource::new(source), FixedSizeBuffer::new())
    }
}

impl<R: io::Read, B: Buffer<u8>> Source<ReadDataSource<R>, B> {
    /// Creates a new `Source` from `Read` and buffer instances.
    #[inline]
    pub fn from_read(source: R, buffer: B) -> Self {
        Self::with_buffer(ReadDataSource::new(source), buffer)
    }
}

impl<I: Iterator, B: Buffer<I::Item>> Source<IteratorDataSource<I>, B>
  where I::Item: Copy + PartialEq {
    /// Creates a new `Source` from `Iterator` and `Buffer` instances.
    #[inline]
    pub fn from_iter(source: I, buffer: B) -> Self {
        Self::with_buffer(IteratorDataSource::new(source), buffer)
    }
}

impl<S: DataSource, B: Buffer<S::Item>> Source<S, B> {
    /// Creates a new `Source` from `DataSource` and `Buffer` instances.
    #[inline]
    pub fn with_buffer(source: S, buffer: B) -> Self {
        Source {
            source:  source,
            buffer:  buffer,
            request: 0,
            state:   INCOMPLETE | AUTOMATIC_FILL,
        }
    }

    /// Attempts to fill this source so it contains at least ``request`` bytes.
    #[inline]
    fn fill_requested(&mut self, request: usize) -> io::Result<usize> {
        let mut read = 0;

        let mut buffer = &mut self.buffer;
        let     source = &mut self.source;

        if buffer.len() < request {
            let diff = request - buffer.len();

            buffer.request_space(diff);

            while buffer.len() < request {
                match try!(buffer.fill(source)) {
                    0 => break,
                    n => read = read + n,
                }
            }
        }

        Ok(read)
    }

    /// Attempts to fill the buffer to satisfy the last call to `parse()`.
    #[inline]
    pub fn fill(&mut self) -> io::Result<usize> {
        // Make sure we actually try to read something in case the buffer is empty
        let req = cmp::max(1, self.request);

        self.fill_requested(req).map(|n| {
            self.state.remove(INCOMPLETE);

            if self.buffer.len() >= req {
                self.state.remove(END_OF_INPUT);
            } else {
                self.state.insert(END_OF_INPUT);
            }

            n
        })
    }

    /// Returns the number of bytes left in the buffer which have not yet been parsed.
    #[inline]
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// If the buffer is empty and the reader has reached the end.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.state.contains(END_OF_INPUT) && self.len() == 0
    }

    /// Returns the capacity of the underlying buffer.
    ///
    /// This is the maximum number of input items the buffer can store.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buffer.capacity()
    }

    /// Borrows the remainder of the buffer.
    #[inline]
    pub fn buffer(&self) -> &[S::Item] {
        &self.buffer
    }

    /// Resets the buffer state, keeping the current buffer contents and cursor position.
    ///
    /// This is useful when streaming data and more data has been made available on a
    /// socket/stream.
    #[inline]
    pub fn reset(&mut self) {
        self.state = ParserState::empty();
    }

    /// Changes the setting automatic fill feature, `true` will make the buffer automatically
    /// call `fill()` on the next call to `parse()` after a `Retry` was encountered.
    // TODO: Make a part of the constructor/builder
    #[inline]
    pub fn set_autofill(&mut self, value: bool) {
        if value {
            self.state.insert(AUTOMATIC_FILL)
        } else {
            self.state.remove(AUTOMATIC_FILL)
        }
    }
}

impl<S: DataSource<Item=u8>, B: Buffer<u8>> io::Read for Source<S, B> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.len() > self.len() {
            try!(self.fill_requested(buf.len()));
        }

        (&self.buffer[..]).read(buf).map(|n| {
            self.buffer.consume(n);

            n
        })
    }
}

impl<S: DataSource<Item=u8>, B: Buffer<u8>> io::BufRead for Source<S, B> {
    #[inline]
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let cap = self.buffer.capacity();

        try!(self.fill_requested(cap));

        Ok(self.buffer())
    }

    #[inline]
    fn consume(&mut self, num: usize) {
        self.buffer.consume(num)
    }
}

impl<'a, S: DataSource, B: Buffer<S::Item>> Stream<'a, 'a> for Source<S, B>
  where S::Item: 'a {
    type Item = S::Item;

    #[inline]
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, StreamError<'a, Self::Item, E>>
      where F: FnOnce(InputBuf<'a, Self::Item>) -> ParseResult<InputBuf<'a, Self::Item>, T, E>,
            T: 'a,
            E: 'a {
        use primitives::Primitives;

        if self.state.contains(INCOMPLETE | AUTOMATIC_FILL) {
            try!(self.fill().map_err(StreamError::IoError));
        }

        if self.is_empty() {
            return Err(StreamError::EndOfInput);
        }

        match f(input::new_buf(input::DEFAULT, &self.buffer)).into_inner() {
            State::Data(remainder, data) => {
                if remainder.is_incomplete() && self.state.contains(END_OF_INPUT) {
                    // We can't accept this since we might have hit a premature end
                    self.request = self.buffer.len() + 1;

                    self.state.insert(INCOMPLETE);

                    Err(StreamError::Retry)
                } else {
                    // TODO: Do something neater with the remainder
                    self.buffer.consume(self.buffer.len() - remainder.len());

                    Ok(data)
                }
            },
            State::Error(mut remainder, err) => {
                if remainder.is_incomplete() {
                    // TODO: How to deal with n, no longer present?
                    self.request = self.buffer.len() + 1;

                    if self.state.contains(END_OF_INPUT) {
                        Err(StreamError::Incomplete(self.request))
                    } else {
                        self.state.insert(INCOMPLETE);

                        Err(StreamError::Retry)
                    }
                } else {
                    // TODO: Do something neater with the remainder
                    // TODO: Detail this behaviour, maybe make it configurable
                    self.buffer.consume(self.buffer.len() - remainder.len());

                    Err(StreamError::ParseError(remainder.consume_remaining(), err))
                }
            },
        }
    }
}

#[cfg(test)]
mod test {
    use std::io;
    use {Input, any, take};
    use Error;
    use buffer::{
        FixedSizeBuffer,
        StreamError,
        Stream,
    };
    use buffer::data_source::ReadDataSource;

    use super::*;

    fn buf(source: &[u8], buffer_length: usize) -> Source<ReadDataSource<io::Cursor<&[u8]>>, FixedSizeBuffer<u8>> {
        Source::with_buffer(ReadDataSource::new(io::Cursor::new(source)), FixedSizeBuffer::with_size(buffer_length))
    }

    #[test]
    #[should_panic]
    fn bufsize_zero() {
        let _ = buf(&b"this is a test"[..], 0);
    }

    #[test]
    fn default_bufsize() {
        let b: Source<_, FixedSizeBuffer<_>> = Source::new(io::Cursor::new(&b"test"[..]));

        assert!(b.capacity() > 0);
    }

    #[test]
    fn empty_buf() {
        let mut n = 0;
        let mut b = Source::new(io::Cursor::new(&b""[..]));

        let r = b.parse(|i| {
            n += 1;

            take(i, 1).bind(|i, _| i.ret::<_, Error<_>>(true))
        });

        assert_eq!(r, Err(StreamError::EndOfInput));
        assert_eq!(n, 0);
    }

    #[test]
    fn fill() {
        let mut n = 0; // Times it has entered the parsing function
        let mut m = 0; // Times it has managed to get past the request for data
        let mut b = buf(&b"test"[..], 1);

        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b't'));
        assert_eq!(n, 1);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 2);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b'e'));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b's'));
        assert_eq!(n, 5);
        assert_eq!(m, 3);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 6);
        assert_eq!(m, 3);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b't'));
        assert_eq!(n, 7);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 8);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::EndOfInput));
        assert_eq!(n, 8);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::EndOfInput));
        assert_eq!(n, 8);
        assert_eq!(m, 4);
    }

    #[test]
    fn fill2() {
        let mut n = 0; // Times it has entered the parsing function
        let mut m = 0; // Times it has managed to get past the request for data
        let mut b = buf(&b"test"[..], 2);

        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b't'));
        assert_eq!(n, 1);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b'e'));
        assert_eq!(n, 2);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b's'));
        assert_eq!(n, 4);
        assert_eq!(m, 3);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b't'));
        assert_eq!(n, 5);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 6);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::EndOfInput));
        assert_eq!(n, 6);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::EndOfInput));
        assert_eq!(n, 6);
        assert_eq!(m, 4);
    }

    #[test]
    fn fill3() {
        let mut n = 0; // Times it has entered the parsing function
        let mut m = 0; // Times it has managed to get past the request for data
        let mut b = buf(&b"test"[..], 3);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"te"[..]));
        assert_eq!(n, 1);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 2);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"st"[..]));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::EndOfInput));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::EndOfInput));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
    }

    #[test]
    fn incomplete() {
        let mut n = 0; // Times it has entered the parsing function
        let mut m = 0; // Times it has managed to get past the request for data
        let mut b = buf(&b"tes"[..], 2);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"te"[..]));
        assert_eq!(n, 1);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 2);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::Incomplete(2)));
        assert_eq!(n, 3);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::Incomplete(2)));
        assert_eq!(n, 4);
        assert_eq!(m, 1);
    }

    #[test]
    fn no_autofill() {
        let mut n = 0; // Times it has entered the parsing function
        let mut m = 0; // Times it has managed to get past the request for data
        let mut b = buf(&b"test"[..], 2);

        b.set_autofill(false);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 1);
        assert_eq!(m, 0);

        assert_eq!(b.fill().unwrap(), 2);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"te"[..]));
        assert_eq!(n, 2);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 3);
        assert_eq!(m, 1);

        assert_eq!(b.fill().unwrap(), 2);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"st"[..]));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 5);
        assert_eq!(m, 2);

        assert_eq!(b.fill().unwrap(), 0);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(StreamError::EndOfInput));
        assert_eq!(n, 5);
        assert_eq!(m, 2);
    }

    #[test]
    fn no_autofill_first() {
        let mut n = 0; // Times it has entered the parsing function
        let mut m = 0; // Times it has managed to get past the request for data
        let mut b = buf(&b"ab"[..], 1);

        b.set_autofill(false);

        assert_eq!(b.fill().unwrap(), 1);

        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b'a'));
        assert_eq!(n, 1);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 2);
        assert_eq!(m, 1);

        assert_eq!(b.fill().unwrap(), 1);

        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b'b'));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::Retry));
        assert_eq!(n, 4);
        assert_eq!(m, 2);

        assert_eq!(b.fill().unwrap(), 0);

        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(StreamError::EndOfInput));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
    }
}
