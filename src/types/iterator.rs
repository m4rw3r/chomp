use std::rc::{Rc, Weak};
use std::cell::RefCell;
use std::collections::VecDeque;

use types::{Buffer, Input};
use primitives::Guard;

/// Struct wrapping an iterator to provide `Input` functionality.
///
/// Note: Allocates an internal buffer to provide peeking and backtracking.
pub struct IteratorInput<I: Iterator> {
    /// Iterator yielding tokens
    iter:   I,
    loaded: VecDeque<I::Item>,
    /// The marked state
    buf:    Weak<RefCell<Vec<I::Item>>>
}

impl<I: Iterator> IteratorInput<I>
  where I::Item: Copy + PartialEq {
    /// Creates a new iterator input.
    pub fn new(i: I) -> Self {
        IteratorInput {
            iter:   i,
            loaded: VecDeque::new(),
            buf:    Weak::new(),
        }
    }
}

// FIXME: Implement
impl<I: Iterator> Input for IteratorInput<I>
  where I::Item: Copy + PartialEq {
    type Token  = I::Item;
    type Buffer = Vec<I::Item>;
    type Marker = ();

    #[inline]
    fn _peek(&mut self, _g: Guard) -> Option<Self::Token> {
        match self.loaded.front().cloned() {
            t @ Some(_) => t,
            None        => self.iter.next().map(|t| {
                self.loaded.push_back(t);

                t
            })
        }
    }

    #[inline]
    fn _pop(&mut self, _g: Guard) -> Option<Self::Token> {
        if self.loaded.is_empty() {
            self.iter.next()
        }
        else {
            self.loaded.pop_front()
        }
    }

    #[inline]
    fn _consume(&mut self, _g: Guard, n: usize) -> Option<Self::Buffer> {
        let additional = n.saturating_sub(self.loaded.len());

        self.loaded.reserve(additional);

        for t in self.iter.by_ref().take(additional) {
            self.loaded.push_back(t);
        }

        if self.loaded.len() >= n {
            Some(self.loaded.drain(..n).collect())
        }
        else {
            None
        }
    }

    #[inline]
    fn _consume_while<F>(&mut self, _g: Guard, mut f: F) -> Self::Buffer
      where F: FnMut(Self::Token) -> bool {
        // TODO: Implement different buffer type which allows for an iterator advancing the cursor
        // instead of using these loops.
        let mut b = Vec::new();

        loop {
            match self.loaded.front().cloned() {
                Some(t) => if f(t) {
                    b.push(self.loaded.pop_front().unwrap());
                }
                else {
                    return b;
                },
                None     => break,
            }
        }

        loop {
            match self.iter.next() {
                Some(t) => if f(t) {
                    b.push(t);
                } else {
                    self.loaded.push_back(t);

                    break;
                },
                None    => break,
            }
        }

        b
    }

    #[inline]
    fn _consume_from(&mut self, _g: Guard, m: Self::Marker) -> Self::Buffer {
        unimplemented!()
        // &m[..m.len() - self.len()]
    }

    #[inline]
    fn _consume_remaining(&mut self, _g: Guard) -> Self::Buffer {
        self.loaded.drain(..).chain(self.iter.by_ref()).collect()
    }

    #[inline]
    fn _mark(&self, _g: Guard) -> Self::Marker {
        unimplemented!()
        // self
    }

    #[inline]
    fn _restore(self, _g: Guard, m: Self::Marker) -> Self {
        unimplemented!()
        // m
    }
}

impl<T: Copy + PartialEq> Buffer for Vec<T> {
    type Token = T;

    fn fold<B, F>(self, a: B, f: F) -> B
      where F: FnMut(B, Self::Token) -> B {
        self.iter().cloned().fold(a, f)
    }

    fn iterate<F>(&self, mut f: F)
      where F: FnMut(Self::Token) {
        for t in self {
            f(*t)
        }
    }

    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn to_vec(&self) -> Vec<Self::Token> {
        self.clone()
    }

    fn into_vec(self) -> Vec<Self::Token> {
        self
    }
}

#[cfg(test)]
mod test {
    use types::Input;
    use primitives::Primitives;
    use super::IteratorInput;

    #[test]
    fn peek_test() {
        let mut i = IteratorInput::new(b"a".iter().cloned());
        assert_eq!(i.peek(), Some(b'a'));
        assert_eq!(i.peek(), Some(b'a'));
        assert_eq!(i.pop(), Some(b'a'));
        assert_eq!(i.peek(), None);
        assert_eq!(i.pop(), None);
    }

    #[test]
    fn consume_test() {
        let mut i = IteratorInput::new(b"abc".iter().cloned());
        assert_eq!(i.consume(0), Some(vec![]));
        assert_eq!(i.consume(1), Some(vec![b'a']));
        assert_eq!(i.consume(2), Some(vec![b'b', b'c']));
        assert_eq!(i.consume(1), None);
        assert_eq!(i.consume(2), None);
        let mut i = IteratorInput::new(b"abc".iter().cloned());
        assert_eq!(i.consume(2), Some(vec![b'a', b'b']));
        assert_eq!(i.consume(2), None);
        assert_eq!(i.consume(1), Some(vec![b'c']));
        assert_eq!(i.consume(1), None);
        let mut i = IteratorInput::new(b"abc".iter().cloned());
        assert_eq!(i.consume(4), None);
        assert_eq!(i.consume(2), Some(vec![b'a', b'b']));
        assert_eq!(i.consume(2), None);
        assert_eq!(i.consume(1), Some(vec![b'c']));
        assert_eq!(i.consume(1), None);
    }

    #[test]
    fn consume_while_test() {
        let mut i = IteratorInput::new(b"abc".iter().cloned());
        assert_eq!(i.consume_while(|x| x != b'c'), vec![b'a', b'b']);
        assert_eq!(i.pop(), Some(b'c'));
        let mut i = IteratorInput::new(b"abc".iter().cloned());
        assert_eq!(i.consume_while(|x| x != b'a'), vec![]);
        assert_eq!(i.pop(), Some(b'a'));
        assert_eq!(i.consume_while(|x| x != b'a'), vec![b'b', b'c']);
        assert_eq!(i.peek(), None);
        assert_eq!(i.pop(), None);
        assert_eq!(i.consume_while(|x| x != b'a'), vec![]);
        assert_eq!(i.peek(), None);
        assert_eq!(i.pop(), None);
        assert_eq!(i.consume_while(|x| x != b'a'), vec![]);
        assert_eq!(i.peek(), None);
        assert_eq!(i.pop(), None);
        let mut i = IteratorInput::new(b"abc".iter().cloned());
        assert_eq!(i.consume(123), None);
        assert_eq!(i.consume_while(|x| x != b'c'), vec![b'a', b'b']);
        assert_eq!(i.pop(), Some(b'c'));
        assert_eq!(i.pop(), None);
        let mut i = IteratorInput::new(b"abc".iter().cloned());
        assert_eq!(i.peek(), Some(b'a'));
        assert_eq!(i.consume_while(|x| x != b'c'), vec![b'a', b'b']);
        assert_eq!(i.pop(), Some(b'c'));
        assert_eq!(i.pop(), None);
    }
}
