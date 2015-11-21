use std::iter;
use std::io;

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
    /// Creates a new buffer with the given ``chunksize`` and ``bufsize``
    pub fn new(source: R, chunksize: usize, bufsize: usize) -> Self {
        // TODO: Error
        assert!(chunksize < bufsize);

        let mut buffer = Vec::with_capacity(bufsize);

        // Fill buffer with zeroes
        buffer.extend(iter::repeat(0).take(bufsize));

        Buffer {
            source: source,
            buffer: buffer,
            chunk:  chunksize,
            used:   0,
            size:   0,
            state:  BufferState::empty(),
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

    /// Returns true if this buffer contains more than the given chunksize.
    ///
    /// Checking this after attempting to drain the buffer using ``iter()`` or
    /// ``iter_buf()`` can indicate the presence of a too long input.
    pub fn has_chunk(&self) -> bool {
        self.size - self.used > self.chunk
    }

    /// Borrows the remainder of the buffer.
    pub fn buffer(&self) -> &[u8] {
        &self.buffer[self.used..self.size]
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
        // TODO: Expected end on EOF

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
                self.used += self.buffer().len() - remainder.buffer().len();

                Ok(data)
            },
            State::Error(remainder, err) => {
                // TODO: Do something neater with the remainder
                self.used += self.buffer().len() - remainder.len();

                Err(ParseError::ParseError(remainder, err))
            },
            State::Incomplete(n) => if self.state.contains(END_OF_INPUT) {
                Err(ParseError::Incomplete(n))
            } else {
                self.state.insert(INCOMPLETE);

                Err(ParseError::Retry)
            },
        }
    }
}
