use std::io;
use std::cmp;

use {Input, ParseResult};
use internal::input;
use internal::{InputModify, State, ParseResultModify};

use buffer::{
    Buffer,
    DataSource,
    FixedSizeBuffer,
    ParseError,
    ReadDataSource,
    Source,
};

const DEFAULT_BUFFER_SIZE: usize = 6 * 1024;

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
pub struct StatefulSource<S: DataSource, B: Buffer<S::Item>> {
    /// Source reader
    source:  S,
    /// Temporary source
    buffer:  B,
    /// The requested amount of bytes to be available for reading from the buffer
    request: usize,
    /// Input state, if end has been reached
    state:   ParserState,
}

impl<R: io::Read> StatefulSource<ReadDataSource<R>, FixedSizeBuffer<u8>> {
    pub fn new(source: R) -> Self {
        Self::with_buffer(ReadDataSource::new(source), FixedSizeBuffer::new(DEFAULT_BUFFER_SIZE))
    }
}

impl<S: DataSource, B: Buffer<S::Item>> StatefulSource<S, B> {
    pub fn with_buffer(source: S, buffer: B) -> Self {
        StatefulSource {
            source:  source,
            buffer:  buffer,
            request: 0,
            state:   INCOMPLETE | AUTOMATIC_FILL,
        }
    }

    /// Attempts to fill this source so it contains at least ``request`` bytes.
    fn fill_requested(&mut self, request: usize) -> io::Result<usize> {
        // Make sure we actually try to read something in case the buffer is empty
        let _request = cmp::max(1, request);

        let mut read = 0;

        let mut buffer = &mut self.buffer;
        let     source = &mut self.source;

        if buffer.len() < _request {
            let diff = _request - buffer.len();

            buffer.request_space(diff);

            while buffer.len() < _request {
                match try!(buffer.fill(source)) {
                    0 => break,
                    n => read = read + n,
                }
            }
        }

        self.state.remove(INCOMPLETE);

        if buffer.len() >= _request {
            self.state.remove(END_OF_INPUT);
        } else {
            self.state.insert(END_OF_INPUT);
        }

        Ok(read)
    }

    /// Attempts to fill the buffer to satisfy the last call to `parse()`.
    pub fn fill(&mut self) -> io::Result<usize> {
        let req = self.request;

        self.fill_requested(req)
    }

    /// Returns the number of bytes left in the buffer.
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    pub fn capacity(&self) -> usize {
        self.buffer.capacity()
    }

    /// Borrows the remainder of the buffer.
    pub fn buffer(&self) -> &[S::Item] {
        &self.buffer
    }

    /// Resets the buffer state, keeping the current buffer contents and cursor position.
    pub fn reset(&mut self) {
        self.state = ParserState::empty();
    }

    /// Changes the setting automatic fill feature, `true` will make the buffer automatically
    /// call `fill()` on the next call to `parse()` after a `Retry` was encountered.
    // TODO: Make a part of the constructor/builder
    pub fn set_autofill(&mut self, value: bool) {
        match value {
            true  => self.state.insert(AUTOMATIC_FILL),
            false => self.state.remove(AUTOMATIC_FILL),
        }
    }
}

impl<S: DataSource<Item=u8>, B: Buffer<u8>> io::Read for StatefulSource<S, B> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.len() > self.len() {
            try!(self.fill_requested(buf.len()));
        }

        return (&self.buffer[..]).read(buf).map(|n| {
            self.buffer.consume(n);

            n
        });
    }
}

impl<S: DataSource<Item=u8>, B: Buffer<u8>> io::BufRead for StatefulSource<S, B> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let cap = self.buffer.capacity();

        try!(self.fill_requested(cap));

        Ok(self.buffer())
    }

    fn consume(&mut self, num: usize) {
        self.buffer.consume(num)
    }
}

impl<'a, S: DataSource, B: Buffer<S::Item>> Source<'a, 'a, S::Item> for StatefulSource<S, B> {
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, ParseError<'a, S::Item, E>>
      where F: FnOnce(Input<'a, S::Item>) -> ParseResult<'a, S::Item, T, E>,
            T: 'a,
            E: 'a {
        if self.state.contains(INCOMPLETE | AUTOMATIC_FILL) {
            let req = self.request;

            try!(self.fill_requested(req).map_err(ParseError::IoError));
        }

        if self.state.contains(END_OF_INPUT) && self.len() == 0 {
            return Err(ParseError::EndOfInput);
        }

        let input_state = if self.state.contains(END_OF_INPUT) { input::END_OF_INPUT } else { input::DEFAULT };

        match f(input::new(input_state, &self.buffer)).internal() {
            State::Data(remainder, data) => {
                // TODO: Do something neater with the remainder
                self.buffer.consume(self.buffer.len() - remainder.buffer().len());

                Ok(data)
            },
            State::Error(remainder, err) => {
                // TODO: Do something neater with the remainder
                // TODO: Detail this behaviour, maybe make it configurable
                self.buffer.consume(self.buffer.len() - remainder.len());

                Err(ParseError::ParseError(remainder, err))
            },
            State::Incomplete(n) => {
                self.request = self.buffer.len() + n;

                if self.state.contains(END_OF_INPUT) {
                    Err(ParseError::Incomplete(self.request))
                } else {
                    self.state.insert(INCOMPLETE);

                    Err(ParseError::Retry)
                }
            },
        }
    }
}

#[cfg(test)]
mod test {
    use std::io;
    use {any, take};
    use {ParseError, Error, Source};
    use buffer::FixedSizeBuffer;
    use buffer::ReadDataSource;

    use super::*;

    fn buf(source: &[u8], buffer_length: usize) -> StatefulSource<ReadDataSource<io::Cursor<&[u8]>>, FixedSizeBuffer<u8>> {
        StatefulSource::with_buffer(ReadDataSource::new(io::Cursor::new(source)), FixedSizeBuffer::new(buffer_length))
    }

    #[test]
    #[should_panic]
    fn bufsize_zero() {
        let _ = buf(&b"this is a test"[..], 0);
    }

    #[test]
    fn default_bufsize() {
        let b = StatefulSource::new(io::Cursor::new(&b"test"[..]));

        assert_eq!(b.capacity(), super::DEFAULT_BUFFER_SIZE);
    }

    #[test]
    fn empty_buf() {
        let mut n = 0;
        let mut b = StatefulSource::new(io::Cursor::new(&b""[..]));

        let r = b.parse(|i| {
            n += 1;

            take(i, 1).bind(|i, _| i.ret::<_, Error<_>>(true))
        });

        assert_eq!(r, Err(ParseError::EndOfInput));
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
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 2);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b'e'));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b's'));
        assert_eq!(n, 5);
        assert_eq!(m, 3);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 6);
        assert_eq!(m, 3);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b't'));
        assert_eq!(n, 7);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 8);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
        assert_eq!(n, 8);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
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
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b's'));
        assert_eq!(n, 4);
        assert_eq!(m, 3);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b't'));
        assert_eq!(n, 5);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 6);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
        assert_eq!(n, 6);
        assert_eq!(m, 4);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
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
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 2);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"st"[..]));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
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
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 2);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::Incomplete(2)));
        assert_eq!(n, 3);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::Incomplete(2)));
        assert_eq!(n, 4);
        assert_eq!(m, 1);
    }

    #[test]
    fn no_autofill() {
        let mut n = 0; // Times it has entered the parsing function
        let mut m = 0; // Times it has managed to get past the request for data
        let mut b = buf(&b"test"[..], 2);

        b.set_autofill(false);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 1);
        assert_eq!(m, 0);

        assert_eq!(b.fill().unwrap(), 2);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"te"[..]));
        assert_eq!(n, 2);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 3);
        assert_eq!(m, 1);

        assert_eq!(b.fill().unwrap(), 2);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"st"[..]));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 5);
        assert_eq!(m, 2);

        assert_eq!(b.fill().unwrap(), 0);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
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
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 2);
        assert_eq!(m, 1);

        assert_eq!(b.fill().unwrap(), 1);

        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Ok(b'b'));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 4);
        assert_eq!(m, 2);

        assert_eq!(b.fill().unwrap(), 0);

        assert_eq!(b.parse(|i| { n += 1; any(i).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
        assert_eq!(n, 4);
        assert_eq!(m, 2);
    }
}
