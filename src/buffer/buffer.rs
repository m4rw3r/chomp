//! Utilities for parsing streams of data.

use std::ops;
use std::ptr;
use std::io;

use buffer::DataSource;

use std::cell::Cell;

const DEFAULT_BUFFER_SIZE: usize = 6 * 1024;

/// Trait all parser buffers implement.
///
/// Enables the consumer to request specific amounts of data and only consume partial parts of the
/// buffer.
pub trait Buffer<I>: ops::Deref<Target=[I]> {
    /// Attempt to fill the buffer using the closure `F`.
    ///
    /// The successful return from `F` should contain the number of items successfully written to
    /// the slice.
    ///
    /// # Notes
    ///
    /// * The returned value must *NOT* be larger than the length of the given slice.
    ///
    /// * Return `0` if no more data is available or if the slice is of zero length.
    ///
    /// * The slice might contain uninitialized memory, do not read from the slice.
    fn fill<S: DataSource<Item=I>>(&mut self, &mut S) -> io::Result<usize>;


    /// Buffer attempts to clear space for additional items.
    fn request_space(&mut self, usize);

    /// Consumes the given amount of bytes, must be less than or equal to `len()`.
    ///
    /// Does not invalidate any borrow of data from self.
    fn consume(&self, items: usize);

    /// Returns the number of bytes left in the buffer.
    fn len(&self) -> usize;

    /// Returns the maximum amount of data which can be stored
    fn capacity(&self) -> usize;
}

/// A fixed size buffer.
///
/// Only allocates when created.
// TODO: Tests
#[derive(Debug, Eq, PartialEq)]
pub struct FixedSizeBuffer<I: Default + Clone> {
    /// Backing memory.
    buffer:    Vec<I>,
    /// Number of items of `buffer` which contain actual data.
    populated: usize,
    /// The number of bytes from the start of the buffer which are used.
    ///
    /// As long as used <= populated it is safe.
    used:      Cell<usize>,
}

impl<I: Default + Clone> FixedSizeBuffer<I> {
    pub fn new() -> Self {
        Self::with_size(DEFAULT_BUFFER_SIZE)
    }

    pub fn with_size(size: usize) -> Self {
        assert!(size > 0);

        FixedSizeBuffer {
            buffer:    vec![Default::default(); size],
            populated: 0,
            used:      Cell::new(0),
        }
    }
}

impl<I: Default + Clone> ops::Deref for FixedSizeBuffer<I> {
    type Target = [I];

    fn deref(&self) -> &[I] {
        &self.buffer[self.used.get()..self.populated]
    }
}

impl<I: Default + Clone> ops::DerefMut for FixedSizeBuffer<I> {
    fn deref_mut(&mut self) -> &mut [I] {
        &mut self.buffer[self.used.get()..self.populated]
    }
}

impl<I: Default + Clone> Buffer<I> for FixedSizeBuffer<I> {
    fn fill<S: DataSource<Item=I>>(&mut self, s: &mut S) -> io::Result<usize> {
        s.read(&mut self.buffer[self.populated..]).map(|n| {
            debug_assert!(self.populated + n <= self.buffer.len());

            self.populated += n;

            n
        })
    }

    fn request_space(&mut self, items: usize) {
        use std::ptr;

        assert!(self.populated >= self.used.get());

        // Only copy if we actually need to free the space
        if self.buffer.len() - self.populated < items {
            unsafe {
                ptr::copy(self.buffer.as_ptr().offset(self.used.get() as isize), self.buffer.as_mut_ptr(), self.populated - self.used.get());
            }

            self.populated -= self.used.get();
            self.used.set(0);
        }
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

/// A buffer which will reallocate to fit the requested amount of data.
///
/// # Note:
///
/// Will not decrease in size.
// TODO: Tests
pub struct GrowingBuffer<I> {
    /// Backing memory.
    buffer:    Vec<I>,
    /// Number of items of `buffer` which contain actual data.
    populated: usize,
    /// Maximal size of the buffer, 0 means infinity.
    limit:     usize,
    /// The number of bytes from the start of the buffer which are used.
    ///
    /// As long as used <= populated it is safe.
    used:      Cell<usize>,
}

impl<I> GrowingBuffer<I> {
    /// Creates a new unlimited `GrowingBuffer`.
    pub fn new() -> Self {
        Self::with_limit(0)
    }

    /// Creates a new `GrowingBuffer` with the specified limit.
    ///
    /// # Note
    ///
    /// The actual amount of allocated memory might be larger than the specified limit, depends on
    /// the allocator.
    pub fn with_limit(limit: usize) -> Self {
        GrowingBuffer {
            buffer:    Vec::new(),
            populated: 0,
            limit:     limit,
            used:      Cell::new(0),
        }
    }
}

impl<I> ops::Deref for GrowingBuffer<I> {
    type Target = [I];

    fn deref(&self) -> &[I] {
        &self.buffer[self.used.get()..self.populated]
    }
}

impl<I> ops::DerefMut for GrowingBuffer<I> {
    fn deref_mut(&mut self) -> &mut [I] {
        &mut self.buffer[self.used.get()..self.populated]
    }
}

impl<I> Buffer<I> for GrowingBuffer<I> {
    fn fill<S: DataSource<Item=I>>(&mut self, s: &mut S) -> io::Result<usize> {
        s.read(&mut self.buffer[self.populated..]).map(|n| {
            debug_assert!(self.populated + n <= self.buffer.len());

            self.populated += n;

            n
        })
    }

    fn request_space(&mut self, items: usize) {
        // If we are over the limit, refuse
        if self.limit != 0 && self.buffer.capacity() > self.limit {
            return;
        }

        if items + self.len() > self.buffer.capacity() {
            // We do not have enough space for the new items, reallocate
            self.buffer.reserve(items);

            let cap = self.buffer.capacity();

            // TODO: Would it be better with a Clone and Default requirement on I?
            // We set the length here to allow fill() to hand out a slice of uninitialized memory
            // to be populated.
            // NOTE: We cannot actually expose this memory to the parser since self.populated will
            // be the upper limit for the deref to slice.
            unsafe {
                self.buffer.set_len(cap);
            }
        }

        // Only copy if we actually need to free the space
        if self.buffer.len() - self.populated < items {
            unsafe {
                ptr::copy(self.buffer.as_ptr().offset(self.used.get() as isize), self.buffer.as_mut_ptr(), self.populated - self.used.get());
            }

            self.populated -= self.used.get();
            self.used.set(0);
        }
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
