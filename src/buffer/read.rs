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

mod inner {
    use std::iter;
    use std::ops;

    use std::cell::Cell;

    /// TODO: Tests
    #[derive(Debug, Eq, PartialEq)]
    pub struct Storage {
        buffer:    Vec<u8>,
        populated: usize,
        /// The number of bytes from the start of the buffer which are used.
        ///
        /// As long as used <= populated it is safe.
        used:      Cell<usize>,
    }

    impl Storage {
        pub fn new(size: usize) -> Self {
            Storage {
                buffer:    iter::repeat(0).take(size).collect(),
                populated: 0,
                used:      Cell::new(0),
            }
        }

        /// Removes used data and moves the unused remainder to the front of self.buffer.
        pub fn drop_used(&mut self) {
            use std::ptr;

            assert!(self.populated >= self.used.get());

            unsafe {
                ptr::copy(self.buffer.as_ptr().offset(self.used.get() as isize), self.buffer.as_mut_ptr(), self.populated - self.used.get());
            }

            self.populated -= self.used.get();
            self.used.set(0);
        }

        /// Attempts to fill the buffer using the closure `F`, the successful return from `F`
        /// should contain the number of bytes successfully written to the slice.
        ///
        /// # Note
        ///
        /// The returned value must *NOT* be larger than the length of the given slice.
        pub fn fill<F, E>(&mut self, f: F) -> Result<usize, E>
          where F: FnOnce(&mut [u8]) -> Result<usize, E> {
            f(&mut self.buffer[self.populated..]).map(|n| {
                self.populated += n;

                n
            })
        }

        /// Consumes the given amount of bytes, must be less than or equal to len.
        ///
        /// Does not invalidate any borrow of data from self.
        pub fn consume(&self, items: usize) {
            debug_assert!(self.used.get() + items <= self.populated);

            self.used.set(self.used.get() + items)
        }

        /// Returns the number of bytes left in the buffer.
        pub fn len(&self) -> usize {
            self.populated - self.used.get()
        }

        /// Returns the maximum amount of data which can be stored
        pub fn capacity(&self) -> usize {
            self.buffer.len()
        }
    }

    impl ops::Deref for Storage {
        type Target = [u8];

        fn deref(&self) -> &[u8] {
            &self.buffer[self.used.get()..self.populated]
        }
    }

    impl ops::DerefMut for Storage {
        fn deref_mut(&mut self) -> &mut [u8] {
            &mut self.buffer[self.used.get()..self.populated]
        }
    }
}

use self::inner::Storage;

const DEFAULT_BUFFER_SIZE: usize = 6 * 1024;

bitflags!{
    flags BufferState: u64 {
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

// TODO: More general variants of the buffer
#[derive(Debug)]
pub struct Buffer<R: Read> {
    /// Source reader
    source:  R,
    storage: Storage,
    /// The requested amount of bytes to be available for reading from the buffer
    request: usize,
    /// Input state, if end has been reached
    state:   BufferState,
}

impl<R: Read> Buffer<R> {
    pub fn new(source: R) -> Self {
        Self::with_size(source, DEFAULT_BUFFER_SIZE)
    }

    pub fn with_size(source: R, bufsize: usize) -> Self {
        assert!(bufsize > 0);

        Buffer {
            source:  source,
            storage: Storage::new(bufsize),
            request: 1,
            state:   INCOMPLETE | AUTOMATIC_FILL,
        }
    }

    /// Attempts to fill this buffer so it contains at least ``request`` bytes.
    fn fill_requested(&mut self, request: usize) -> io::Result<usize> {
        let mut read = 0;

        let mut storage = &mut self.storage;
        let     source  = &mut self.source;

        if storage.len() < request {
            storage.drop_used();

            while storage.len() < request {
                match try!(storage.fill(|b| source.read(b))) {
                    0 => break,
                    n => read = read + n,
                }
            }
        }

        self.state.remove(INCOMPLETE);

        if read >= request {
            self.state.remove(END_OF_INPUT);
        } else {
            self.state.insert(END_OF_INPUT);
        }

        Ok(read)
    }

    pub fn fill(&mut self) -> io::Result<usize> {
        let req = self.request;

        self.fill_requested(req)
    }

    /// Returns the number of bytes left in the buffer.
    pub fn len(&self) -> usize {
        self.storage.len()
    }

    pub fn capacity(&self) -> usize {
        self.storage.capacity()
    }

    /// Borrows the remainder of the buffer.
    pub fn buffer(&self) -> &[u8] {
        &self.storage
    }

    /// Resets the buffer state, keeping the current buffer contents and cursor position.
    pub fn reset(&mut self) {
        self.state = BufferState::empty();
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

impl<R: Read> Read for Buffer<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.len() > self.len() {
            try!(self.fill_requested(buf.len()));
        }

        return (&self.storage[..]).read(buf).map(|n| {
            self.storage.consume(n);

            n
        });
    }
}

impl<R: Read> BufRead for Buffer<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let cap = self.storage.capacity();

        try!(self.fill_requested(cap));

        Ok(self.buffer())
    }

    fn consume(&mut self, num: usize) {
        self.storage.consume(num)
    }
}

impl<'a, R: Read> Source<'a, 'a, u8> for Buffer<R> {
    fn parse<F, T, E>(&'a mut self, f: F) -> Result<T, ParseError<'a, u8, E>>
      where F: FnOnce(Input<'a, u8>) -> ParseResult<'a, u8, T, E>,
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

        match f(input::new(input_state, &self.storage)).internal() {
            State::Data(remainder, data) => {
                // TODO: Do something neater with the remainder
                self.storage.consume(self.storage.len() - remainder.buffer().len());

                Ok(data)
            },
            State::Error(remainder, err) => {
                // TODO: Do something neater with the remainder
                // TODO: Detail this behaviour, maybe make it configurable
                self.storage.consume(self.storage.len() - remainder.len());

                Err(ParseError::ParseError(remainder, err))
            },
            State::Incomplete(n) => {
                self.request = self.storage.len() + n;

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

    use super::*;

    #[test]
    #[should_panic]
    fn bufsize_zero() {
        let _ = Buffer::with_size(io::Cursor::new(&b"this is a test"[..]), 0);
    }

    #[test]
    fn default_bufsize() {
        let b = Buffer::new(io::Cursor::new(&b"test"[..]));

        assert_eq!(b.capacity(), super::DEFAULT_BUFFER_SIZE);
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

    #[test]
    fn fill2() {
        let mut n = 0; // Times it has entered the parsing function
        let mut m = 0; // Times it has managed to get past the request for data
        let mut b = Buffer::with_size(io::Cursor::new(&b"test"[..]), 2);

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
        let mut b = Buffer::with_size(io::Cursor::new(&b"test"[..]), 3);

        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"te"[..]));
        assert_eq!(n, 1);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::Retry));
        assert_eq!(n, 2);
        assert_eq!(m, 1);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Ok(&b"st"[..]));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
        assert_eq!(b.parse(|i| { n += 1; take(i, 2).inspect(|_| m += 1) }), Err(ParseError::EndOfInput));
        assert_eq!(n, 3);
        assert_eq!(m, 2);
    }

    #[test]
    fn incomplete() {
        let mut n = 0; // Times it has entered the parsing function
        let mut m = 0; // Times it has managed to get past the request for data
        let mut b = Buffer::with_size(io::Cursor::new(&b"tes"[..]), 2);

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
        let mut b = Buffer::with_size(io::Cursor::new(&b"test"[..]), 2);

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
}
