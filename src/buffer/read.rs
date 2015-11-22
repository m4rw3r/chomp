use std::iter;
use std::io;
use std::cmp;

use std::io::Read;
use std::io::BufRead;

use ParseResult;
use Input;
use buffer::ParseError;
use buffer::Source;
use internal::input;
use internal::State;
use internal::ParseResultModify;
use internal::InputModify;

const DEFAULT_BUFFER_SIZE: usize = 6 * 1024;

bitflags!{
    flags BufferState: u64 {
        const INCOMPLETE   = 1,
        const END_OF_INPUT = 2,
    }
}

// TODO: More general variants of the buffer
#[derive(Debug)]
pub struct Buffer<R: Read> {
    /// Source reader
    source: R,
    /// Internal buffer
    buffer: Vec<u8>,
    /// The requested amount of bytes to be available for reading from the buffer
    chunk:  usize,
    /// The number of bytes from the start of the buffer which has been consumed
    used:   usize,
    /// The number of bytes from the start of the buffer which have been populated
    size:   usize,
    /// Input state, if end has been reached
    state:  BufferState,
}

impl<R: Read> Buffer<R> {
    pub fn new(source: R) -> Self {
        Self::with_size(source, DEFAULT_BUFFER_SIZE)
    }

    pub fn with_size(source: R, bufsize: usize) -> Self {
        Self::with_size_and_chunk(source, bufsize, bufsize / 4)
    }

    /// Creates a new buffer with the given ``chunksize`` and ``bufsize``
    pub fn with_size_and_chunk(source: R, bufsize: usize, chunksize: usize) -> Self {
        assert!(bufsize > 0);
        assert!(bufsize > chunksize);

        Buffer {
            source: source,
            buffer: iter::repeat(0).take(bufsize).collect(),
            chunk:  cmp::max(chunksize, 1),
            used:   0,
            size:   0,
            state:  INCOMPLETE,
        }
    }

    /// Removes used data and moves the unused remainder to the front of self.buffer.
    fn drop_used(&mut self) {
        use std::ptr;

        assert!(self.size >= self.used);

        unsafe {
            ptr::copy(self.buffer.as_ptr().offset(self.used as isize), self.buffer.as_mut_ptr(), self.size - self.used);
        }

        self.size = self.size - self.used;
        self.used = 0;
    }

    /// Attempts to fill this buffer so it contains at least ``chunksize`` bytes.
    pub fn fill(&mut self) -> io::Result<usize> {
        let mut read = 0;

        if self.size < self.used + self.chunk {
            self.drop_used();
        }

        while self.size + read < self.chunk {
            match try!(self.source.read(&mut self.buffer[self.size + read..])) {
                0 => break,
                n => read = read + n,
            }
        }

        self.size = self.size + read;

        Ok(read)
    }

    /// Returns the number of bytes left in the buffer.
    pub fn len(&self) -> usize {
        self.size - self.used
    }

    /// Borrows the remainder of the buffer.
    pub fn buffer(&self) -> &[u8] {
        &self.buffer[self.used..self.size]
    }

    /// Resets the buffer state, keeping the current buffer contents and cursor position.
    pub fn reset(&mut self) {
        self.state = BufferState::empty();
    }
}

impl<R: Read> Read for Buffer<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.len() > self.size - self.used {
            try!(self.fill());
        }

        return (&self.buffer[self.used..self.size]).read(buf).map(|n| {
            self.used = self.used + n;

            n
        });
    }
}

impl<R: Read> BufRead for Buffer<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        try!(self.fill());

        Ok(self.buffer())
    }

    fn consume(&mut self, num: usize) {
        self.used = self.used + num
    }
}

impl<'a, R: Read> Source<'a, 'a, u8> for Buffer<R> {
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, ParseError<'a, u8, E>>
      where F: FnOnce(Input<'a, u8>) -> ParseResult<'a, u8, T, E>,
            T: 'a,
            E: 'a {
        if self.state.contains(INCOMPLETE) {
            match self.fill() {
                Ok(0)    => self.state.insert(END_OF_INPUT),
                Ok(_)    => self.state.remove(END_OF_INPUT),
                Err(err) => return Err(ParseError::IoError(err)),
            }

            self.state.remove(INCOMPLETE)
        }

        if self.state.contains(END_OF_INPUT) && self.len() == 0 {
            return Err(ParseError::EndOfInput);
        }

        let input_state = if self.state.contains(END_OF_INPUT) { input::END_OF_INPUT } else { input::DEFAULT };
        // Inline version of self.buffer() to satisfy borrowck
        let buffer      = &self.buffer[self.used..self.size];

        match f(input::new(input_state, buffer)).internal() {
            State::Data(remainder, data) => {
                // TODO: Do something neater with the remainder
                self.used += buffer.len() - remainder.buffer().len();

                Ok(data)
            },
            State::Error(remainder, err) => {
                // TODO: Do something neater with the remainder
                self.used += buffer.len() - remainder.len();

                Err(ParseError::ParseError(remainder, err))
            },
            State::Incomplete(n) => if self.state.contains(END_OF_INPUT) {
                // TODO: Use the number here to at least inform the next read of how much data is
                // needed.
                Err(ParseError::Incomplete(n))
            } else {
                self.state.insert(INCOMPLETE);

                Err(ParseError::Retry)
            },
        }
    }
}

#[cfg(test)]
mod test {
    use std::io;
    use {any, take};
    use {ParseError, Error, Source};

    use super::*;

    #[test]
    #[should_panic]
    fn bufsize_lt_chunksize() {
        let _ = Buffer::with_size_and_chunk(io::Cursor::new(&b"this is a test"[..]), 64, 128);
    }

    #[test]
    fn empty_buf() {
        let mut n = 0;
        let mut b = Buffer::new(io::Cursor::new(&b""[..]));

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
        let mut b = Buffer::with_size(io::Cursor::new(&b"test"[..]), 1);

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
}
