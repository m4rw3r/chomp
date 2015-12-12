//! Internal iterator for applying a parser multiple times on a buffer.
//!
//! This iterator also exposes the `State` after iteration which contains the remainder of the
//! input as well as any error or incomplete state.

use std::marker::PhantomData;

use {Input, ParseResult};
use primitives::{InputClone, IntoInner, State};

pub enum EndStateTill<'a, I, E>
  where I: 'a {
    Error(&'a [I], E),
    Incomplete(usize),
    EndSuccess,
}

/// Iterator used by ``many_till`` and ``many1``.
pub struct IterTill<'a, I, T, U, E, F, P, N>
  where I: 'a,
        T: 'a,
        E: 'a,
        U: 'a,
        N: 'a,
        P: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E>,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, N> {
    state:  EndStateTill<'a, I, E>,
    parser: P,
    end:    F,
    buf:    Input<'a, I>,
    _t:     PhantomData<(T, U, N)>,
}

impl<'a, I, T, U, E, F, P, N> IterTill<'a, I, T, U, E, F, P, N>
  where I: 'a,
        T: 'a,
        E: 'a,
        U: 'a,
        N: 'a,
        P: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E>,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, N> {
    #[inline]
    pub fn new(buffer: Input<'a, I>, parser: P, end: F) -> Self {
        IterTill {
            state:  EndStateTill::Incomplete(0),
            parser: parser,
            end:    end,
            buf:    buffer,
            _t:     PhantomData,
        }
    }

    /// Destructures the iterator returning the position just after the last successful parse as
    /// well as the state of the last attempt to parse data.
    #[inline]
    pub fn end_state(self) -> (Input<'a, I>, EndStateTill<'a, I, E>) {
        (self.buf, self.state)
    }
}

impl<'a, I, T, U, E, F, P, N> Iterator for IterTill<'a, I, T, U, E, F, P, N>
  where I: 'a,
        T: 'a,
        E: 'a,
        U: 'a,
        N: 'a,
        P: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E>,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let State::Data(b, _) = (self.end)(self.buf.clone()).into_inner() {
            self.buf   = b;
            self.state = EndStateTill::EndSuccess;

            return None
        }

        match (self.parser)(self.buf.clone()).into_inner() {
            State::Data(b, v) => {
                self.buf = b;

                Some(v)
            },
            State::Error(b, e) => {
                self.state = EndStateTill::Error(b, e);

                None
            },
            State::Incomplete(n) => {
                self.state = EndStateTill::Incomplete(n);

                None
            },
        }
    }
}
