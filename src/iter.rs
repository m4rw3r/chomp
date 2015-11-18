//! Internal iterator for applying a parser multiple times on a buffer.

use std::marker::PhantomData;

use {ParseResult, Input};
use internal::State;
use internal::{InputModify, ParseResultModify};

pub enum EndState<'a, I, E>
  where I: 'a {
    Error(&'a [I], E),
    Incomplete(usize),
}

/// Iterator used by ``many`` and ``many1``.
pub struct Iter<'a, I, T, E, F>
  where I: 'a,
        T: 'a,
        E: 'a,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
    state:  EndState<'a, I, E>,
    parser: F,
    buf:    Input<'a, I>,
    _t:     PhantomData<T>,
}

impl<'a, I, T, E, F> Iter<'a, I, T, E, F>
  where I: 'a,
        T: 'a,
        E: 'a,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
    #[inline]
    pub fn new(buffer: Input<'a, I>, parser: F) -> Iter<'a, I, T, E, F> {
        Iter{
            state:  EndState::Incomplete(0),
            parser: parser,
            buf:    buffer,
            _t:     PhantomData,
        }
    }

    /// Destructures the iterator returning the position just after the last successful parse as
    /// well as the state of the last attempt to parse data.
    #[inline]
    pub fn end_state(self) -> (Input<'a, I>, EndState<'a, I, E>) {
        (self.buf, self.state)
    }
}

impl<'a, I, T, E, F> Iterator for Iter<'a, I, T, E, F>
  where I: 'a,
        T: 'a,
        E: 'a,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match (self.parser)(self.buf.clone_input()).internal() {
            State::Data(b, v) => {
                self.buf = b;

                Some(v)
            },
            State::Error(b, e) => {
                self.state = EndState::Error(b, e);

                None
            },
            State::Incomplete(n) => {
                self.state = EndState::Incomplete(n);

                None
            },
        }
    }
}
