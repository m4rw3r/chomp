use std::marker::PhantomData;
use std::iter::FromIterator;
use std::ops::{
    Range,
    RangeFrom,
    RangeFull,
    RangeTo,
};
use std::cmp::max;

use {Input, ParseResult};
use primitives::{InputClone, InputBuffer, IntoInner, State};

/// Internal macro to provide speedup for `FromIterator::from_iter`.
///
/// Needed as of rustc 1.7.0-nightly (81ae8be71 2015-12-09).
macro_rules! run_from_iter(
    ( $iter:ident as $r_ty:ty ) => {
        {
            // Dummy variable to tie the scope of the iteration into the current scope,
            // this causes rustc to inline `Iterator::next` into this scope including
            // `FromIterator::from_iter`.
            // This is probably how it works, #[inline] and #[inline(always)] do not affect it as
            // of rustc 1.7.0-nightly (81ae8be71 2015-12-09).
            let mut item = false;

            // the inspect() is useless here, but ties the inner scope of the loop to the current
            // scope which will make it inline `Iterator::next`.
            let result: T = FromIterator::from_iter($iter.by_ref().inspect(|_| item = true));

            // Oddly enough, no inspect() is much much slower:
            //
            // ```
            // let result: $r_ty = FromIterator::from_iter($iter.by_ref());
            // ```
            //
            // The above code is only faster in very very small benchmarks, anything larger than
            // the benchmarks for many (ie. multiple `many(i, any)`) will most likely be slower
            // when using the above line.

            // The performance difference is definitely noticeable in benchmarks, parsing 10k bytes of
            // any type and just storing them in a Vec is 10x slower on current nightly
            // (rustc 1.7.0-nightly (81ae8be71 2015-12-09)).

            (result, $iter.end_state())
        }
    }
);

/// Macro to implement a parser iterator, it provides the ability to add an extra state variable
/// into it and also provide a size_hint as well as a pre- and on-next hooks.
macro_rules! impl_iter {
    ( $iter_name:ident ( $data_ty:ty ) {
        size_hint($size_hint_self:ident) $size_hint:block

        next($next_self:ident) {
            pre $pre_next:block
            on  $on_next:block
        }
    } ) => {
        enum EndState<'a, I, E>
          where I: 'a {
            Error(&'a [I], E),
            Incomplete(usize),
        }

        struct $iter_name<'a, I, T, E, F>
          where I: 'a,
                T: 'a,
                E: 'a,
                F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
            /// Last state of the parser
            state:  EndState<'a, I, E>,
            /// Parser to execute once for each iteration
            parser: F,
            /// Remaining buffer
            buf:    Input<'a, I>,
            /// Nested state
            data:   $data_ty,
            _t:     PhantomData<T>,
        }

        impl<'a, I, T, E, F> $iter_name<'a, I, T, E, F>
          where I: 'a,
                T: 'a,
                E: 'a,
                F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
            #[inline(always)]
            fn end_state(self) -> (Input<'a, I>, $data_ty, EndState<'a, I, E>) {
                (self.buf, self.data, self.state)
            }
        }

        impl<'a, I, T, E, F> Iterator for $iter_name<'a, I, T, E, F>
          where I: 'a,
                T: 'a,
                E: 'a,
                F: FnMut(Input<'a, I>) -> ParseResult<'a, I, T, E> {
            type Item = T;

            #[inline(always)]
            fn size_hint(&$size_hint_self) -> (usize, Option<usize>) {
                $size_hint
            }

            #[inline(always)]
            fn next(&mut $next_self) -> Option<Self::Item> {
                $pre_next

                match ($next_self.parser)($next_self.buf.clone()).into_inner() {
                    State::Data(b, v) => {
                        $next_self.buf    = b;

                        $on_next

                        Some(v)
                    },
                    State::Error(b, e) => {
                        $next_self.state = EndState::Error(b, e);

                        None
                    },
                    State::Incomplete(n) => {
                        $next_self.state = EndState::Incomplete(n);

                        None
                    },
                }
            }
        }
    };
    ( $iter_name:ident ( $data_ty:ty ) {
        size_hint($size_hint_self:ident) $size_hint:block
    } ) => {
        impl_iter!($iter_name ( $data_ty ) {
            size_hint ( $size_hint_self ) $size_hint

            next(self) {
                pre {}
                on  {}
            }
        })
    };
}

/// Trait for iterating a parser based on a range.
pub trait BoundedRange {
    #[inline]
    fn parse<'a, I, T, E, F, U>(&self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            T: FromIterator<U>;
}

impl BoundedRange for Range<usize> {
    #[inline]
    fn parse<'a, I, T, E, F, U>(&self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            T: FromIterator<U> {
        impl_iter!(ToIter((usize, usize)) {
            size_hint(self) {
                (self.data.0, Some(self.data.1))
            }

            next(self) {
                pre {
                    if self.data.1 == 0 {
                        return None;
                    }
                }
                on {
                    self.data.0  = if self.data.0 == 0 { 0 } else { self.data.0 - 1 };
                    self.data.1 -= 1;
                }
            }
        });

        let mut iter = ToIter {
            state:  EndState::Incomplete(1),
            parser: f,
            buf:    i,
            // Range is closed on left side, open on right, ie. [self.start, self.end)
            data:   (self.start, max(self.end, 1) - 1),
            _t:     PhantomData,
        };

        let (result, state) = run_from_iter!(iter as T);

        match state {
            // Got all occurrences of the parser
            (s, (0, 0), _) => s.ret(result),
            // Ok, last parser failed and we have reached minimum, we have iterated all.
            // Return remainder of buffer and the collected result
            (s, (0, _), EndState::Error(_, _))   => s.ret(result),
            // Nested parser incomplete but reached at least minimum, propagate if not at end
            (s, (0, _), EndState::Incomplete(n)) => if s.buffer().len() == 0 && s.is_last_slice() {
                s.ret(result)
            } else {
                s.incomplete(n)
            },
            // Did not reach minimum, propagate
            (s, (_, _), EndState::Error(b, e))   => s.replace(b).err(e),
            (s, (_, _), EndState::Incomplete(n)) => s.incomplete(n),
        }
    }
}

impl BoundedRange for RangeFrom<usize> {
    #[inline]
    fn parse<'a, I, T, E, F, U>(&self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            T: FromIterator<U> {
        impl_iter!(FromIter(usize) {
            size_hint(self) {
                (self.data, None)
            }

            next(self) {
                pre {}
                on  {
                    self.data = if self.data == 0 { 0 } else { self.data - 1 };
                }
            }
        });

        let mut iter = FromIter {
            state:  EndState::Incomplete(1),
            parser: f,
            buf:    i,
            // Inclusive
            data:   self.start,
            _t:     PhantomData,
        };

        let (result, state) = run_from_iter!(iter as T);

        match state {
            // We got at least n items
            (s, 0, EndState::Error(_, _))   => s.ret(result),
            // Nested parser incomplete, propagate if not at end
            (s, 0, EndState::Incomplete(n)) => if s.buffer().len() == 0 && s.is_last_slice() {
                s.ret(result)
            } else {
                s.incomplete(n)
            },
            // Items still remaining, propagate
            (s, _, EndState::Error(b, e))   => s.replace(b).err(e),
            (s, _, EndState::Incomplete(n)) => s.incomplete(n),
        }
    }
}

impl BoundedRange for RangeFull {
    #[inline]
    fn parse<'a, I, T, E, F, U>(&self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            T: FromIterator<U> {
        impl_iter!(ManyIter(()) {
            size_hint(self) {
                (0, None)
            }
        });

        let mut iter = ManyIter {
            state:  EndState::Incomplete(1),
            parser: f,
            buf:    i,
            // No data required
            data:   (),
            _t:     PhantomData,
        };

        let (result, state) = run_from_iter!(iter as T);

        match state {
            (s, (), EndState::Error(_, _))   => s.ret(result),
            // Nested parser incomplete, propagate if not at end
            (s, (), EndState::Incomplete(n)) => if s.buffer().len() == 0 && s.is_last_slice() {
                s.ret(result)
            } else {
                s.incomplete(n)
            },
        }
    }
}

impl BoundedRange for RangeTo<usize> {
    #[inline]
    fn parse<'a, I, T, E, F, U>(&self, i: Input<'a, I>, f: F) -> ParseResult<'a, I, T, E>
      where I: Copy,
            U: 'a,
            F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
            T: FromIterator<U> {
        impl_iter!(ToIter(usize) {
            size_hint(self) {
                (0, Some(self.data))
            }

            next(self) {
                pre {
                    if self.data == 0 {
                        return None;
                    }
                }
                on {
                    self.data  -= 1;
                }
            }
        });

        let mut iter = ToIter {
            state:  EndState::Incomplete(1),
            parser: f,
            buf:    i,
            // Exclusive range [0, end)
            data:   max(self.end, 1) - 1,
            _t:     PhantomData,
        };

        let (result, state) = run_from_iter!(iter as T);

        match state {
            // Either error or incomplete after the end
            (s, 0, _)                       => s.ret(result),
            // Inside of range, never outside
            (s, _, EndState::Error(_, _))   => s.ret(result),
            // Nested parser incomplete, propagate if not at end
            (s, _, EndState::Incomplete(n)) => if s.buffer().len() == 0 && s.is_last_slice() {
                s.ret(result)
            } else {
                s.incomplete(n)
            },
        }
    }
}

#[inline]
pub fn many<'a, I, T, E, F, U, R>(i: Input<'a, I>, r: R, f: F) -> ParseResult<'a, I, T, E>
  where I: Copy,
        R: BoundedRange,
        U: 'a,
        F: FnMut(Input<'a, I>) -> ParseResult<'a, I, U, E>,
        T: FromIterator<U> {
    BoundedRange::parse(&r, i, f)
}
