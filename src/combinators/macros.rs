
/// Macro to implement and run a parser iterator, it provides the ability to add an extra state
/// variable into it and also provide a size_hint as well as a pre- and on-next hooks.
macro_rules! run_iter {
    (
        input:     $input:expr,
        parser:    $parser:expr,
        state:     $data_ty:ty : $data:expr,

        size_hint($size_hint_self:ident) $size_hint:block
        next($next_self:ident) {
            pre $pre_next:block
            on  $on_next:block
        }

        => $result:ident : $t:ty {
             $($pat:pat => $arm:expr),*
        }
    ) => { {
        enum EndState<M, E> {
            // We have an interest to maybe backtrack to last good state in the case of an error.
            Error(M, E),
            Incomplete(usize),
        }

        struct Iter<I: Input, T, E, F>
          where F: FnMut(I) -> ParseResult<I, T, E> {
            /// Last state of the parser
            state:  EndState<I::Marker, E>,
            /// Parser to execute once for each iteration
            parser: F,
            /// Remaining buffer
            // TODO: Use UnsafeCell or similar to omit branches, only way to avoid this being set
            // on next read would be panic I think? (since self is mutably borrowed already by
            // next)
            buf:    Option<I>,
            /// Nested state
            data:   $data_ty,
            _t:     PhantomData<T>,
        }

        impl<I: Input, T, E, F> Iter<I, T, E, F>
          where F: FnMut(I) -> ParseResult<I, T, E> {
            #[inline]
            fn end_state(self) -> (I, $data_ty, EndState<I::Marker, E>) {
                (self.buf.unwrap(), self.data, self.state)
            }
        }

        impl<I: Input, T, E, F> Iterator for Iter<I, T, E, F>
          where F: FnMut(I) -> ParseResult<I, T, E> {
            type Item = T;

            #[inline]
            fn size_hint(&$size_hint_self) -> (usize, Option<usize>) {
                $size_hint
            }

            #[inline]
            fn next(&mut $next_self) -> Option<Self::Item> {
                $pre_next

                // TODO: Remove the branches here (ie. take + unwrap)
                let i = $next_self.buf.take().unwrap();
                let m = i.mark();
                match ($next_self.parser)(i).into_inner() {
                    State::Data(b, v) => {
                        $next_self.buf = Some(b);

                        $on_next

                        Some(v)
                    },
                    State::Error(b, e) => {
                        $next_self.buf   = Some(b);
                        $next_self.state = EndState::Error(m, e);

                        None
                    },
                    State::Incomplete(b, n) => {
                        $next_self.buf   = Some(b);
                        $next_self.state = EndState::Incomplete(n);

                        None
                    },
                }
            }
        }

        let mut iter = Iter {
            state:  EndState::Incomplete(1),
            parser: $parser,
            buf:    Some($input),
            data:   $data,
            _t:     PhantomData,
        };

        let $result: $t = FromIterator::from_iter(iter.by_ref());

        match iter.end_state() {
            $($pat => $arm),*
        }
    } }
}

/// Version of run_iter which allows for an additional parser to be run which can terminate
/// iteration early.
macro_rules! run_iter_till {
    (
        input:     $input:expr,
        parser:    $parser:expr,
        end:       $end:expr,
        state:     $data_ty:ty : $data:expr,

        size_hint($size_hint_self:ident) $size_hint:block
        next($next_self:ident) {
            pre $pre_next:block
            on  $on_next:block
        }

        => $result:ident : $t:ty {
             $($pat:pat => $arm:expr),*
        }
    ) => { {
        enum EndStateTill<'a, I, E>
          where I: 'a {
            Error(&'a [I], E),
            Incomplete(usize),
            EndSuccess,
        }

        /// Iterator used by ``many_till`` and ``many1``.
        struct IterTill<'a, I, T, U, E, F, P, N>
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
            data:   $data_ty,
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
            /// Destructures the iterator returning the position just after the last successful parse as
            /// well as the state of the last attempt to parse data.
            #[inline]
            fn end_state(self) -> (Input<'a, I>, $data_ty, EndStateTill<'a, I, E>) {
                (self.buf, self.data, self.state)
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
            fn size_hint(&$size_hint_self) -> (usize, Option<usize>) {
                $size_hint
            }

            #[inline]
            fn next(&mut $next_self) -> Option<Self::Item> {
                $pre_next

                match ($next_self.parser)($next_self.buf.clone()).into_inner() {
                    State::Data(b, v) => {
                        $next_self.buf = b;

                        $on_next

                        Some(v)
                    },
                    State::Error(b, e) => {
                        $next_self.state = EndStateTill::Error(b, e);

                        None
                    },
                    State::Incomplete(n) => {
                        $next_self.state = EndStateTill::Incomplete(n);

                        None
                    },
                }
            }
        }

        let mut iter = IterTill {
            state:  EndStateTill::Incomplete(1),
            parser: $parser,
            end:    $end,
            buf:    $input,
            data:   $data,
            _t:     PhantomData,
        };

        let $result: $t = FromIterator::from_iter(iter.by_ref());

        match iter.end_state() {
            $($pat => $arm),*
        }
    } }
}

/// Used with `run_iter_till!` macro to attempt to end iteration early. If the test succeeds the
/// buffer position will be updated and the state set to `EndStateTill::EndSuccess` and a `None`
/// will be returned, stopping the iteration. If the test fails execution continues.
macro_rules! iter_till_end_test {
    ( $the_self:ident ) => { {
        if let State::Data(b, _) = ($the_self.end)($the_self.buf.clone()).into_inner() {
            $the_self.buf   = b;
            $the_self.state = EndStateTill::EndSuccess;

            return None
        }
    } }
}
