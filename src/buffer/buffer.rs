use std::ops;

use std::cell::Cell;

pub trait Buffer<I>: ops::Deref<Target=[I]> {
    /// Attempts to fill the buffer using the closure `F`, the successful return from `F`
    /// should contain the number of items successfully written to the slice.
    ///
    /// # Note
    ///
    /// The returned value must *NOT* be larger than the length of the given slice.
    ///
    /// Return `0` if no more data is available or if the slice is of zero length.
    fn fill<F, E>(&mut self, f: F) -> Result<usize, E>
      where F: FnOnce(&mut [I]) -> Result<usize, E>;


    /// Buffer attempts to clear space.
    fn request_space(&mut self, usize);

    /// Consumes the given amount of bytes, must be less than or equal to len.
    ///
    /// Does not invalidate any borrow of data from self.
    fn consume(&self, items: usize);

    /// Returns the number of bytes left in the buffer.
    fn len(&self) -> usize;

    /// Returns the maximum amount of data which can be stored
    fn capacity(&self) -> usize;
}

/// TODO: Tests
#[derive(Debug, Eq, PartialEq)]
pub struct FixedSizeBuffer {
    buffer:    Vec<u8>,
    populated: usize,
    /// The number of bytes from the start of the buffer which are used.
    ///
    /// As long as used <= populated it is safe.
    used:      Cell<usize>,
}

impl FixedSizeBuffer {
    pub fn new(size: usize) -> Self {
        FixedSizeBuffer {
            buffer:    vec![0; size],
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
}

impl ops::Deref for FixedSizeBuffer {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.buffer[self.used.get()..self.populated]
    }
}

impl ops::DerefMut for FixedSizeBuffer {
    fn deref_mut(&mut self) -> &mut [u8] {
        &mut self.buffer[self.used.get()..self.populated]
    }
}

impl Buffer<u8> for FixedSizeBuffer {
    fn fill<F, E>(&mut self, f: F) -> Result<usize, E>
      where F: FnOnce(&mut [u8]) -> Result<usize, E> {
        f(&mut self.buffer[self.populated..]).map(|n| {
            self.populated += n;

            n
        })
    }

    fn request_space(&mut self, _items: usize) {
        self.drop_used();
    }

    fn consume(&self, items: usize) {
        debug_assert!(self.used.get() + items <= self.populated);

        self.used.set(self.used.get() + items)
    }

    fn len(&self) -> usize {
        self.populated - self.used.get()
    }

    fn capacity(&self) -> usize {
        self.buffer.len()
    }
}
