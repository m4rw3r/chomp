macro_rules! many_iter {
    (
        doc:         $doc:expr,
        struct_name: $name:ident,
        state:       $data_ty:ty,

        size_hint($size_hint_self:ident) $size_hint:block
        next($next_self:ident) {
            pre $pre_next:block
            on  $on_next:block
        }

        => $result:ident : $t:ty {
             $($pat:pat => $arm:expr),*$(,)*
        }
    ) => {
        #[doc=$doc]
        pub struct $name<I, F, P, T>
          where I: Input,
                F: FnMut() -> P,
                T: FromIterator<P::Output>,
                P: Parser<I> {
            /// Parser to execute once for each iteration
            parser_ctor: F,
            /// Nested state
            data:      $data_ty,
            _i:        PhantomData<I>,
            _t:        PhantomData<T>,
            _p:        PhantomData<P>,
        }

        impl<I, F, P, T> Parser<I> for $name<I, F, P, T>
          where I: Input,
                F: FnMut() -> P,
                P: Parser<I>,
                T: FromIterator<P::Output> {
            type Output = T;
            type Error  = P::Error;

            #[inline]
            fn parse(self, i: I) -> (I, Result<T, P::Error>) {
                /// Iterator used to run the parser multiple times
                struct ParserIterator<I: Input, F, P, T>
                  where F: FnMut() -> P,
                        P: Parser<I> {
                    /// Last state of the parser
                    state:  Option<P::Error>,
                    /// Parser constructor function to execute once for each iteration to obtain
                    /// a new parser to run for each iteration
                    parser_ctor: F,
                    /// Remaining buffer
                    ///
                    /// Wrapped in option to prevent two calls to destructors.
                    buf:    Option<I>,
                    /// Last good state.
                    mark:   I::Marker,
                    /// Nested state
                    data:   $data_ty,
                    _i:     PhantomData<I>,
                    _t:     PhantomData<T>,
                    _p:     PhantomData<P>,
                }

                impl<I: Input, F, P, T> ParserIterator<I, F, P, T>
                  where F: FnMut() -> P,
                        P: Parser<I> {
                    #[inline]
                    fn end_state(self) -> (I, $data_ty, I::Marker, Option<P::Error>) {
                        // TODO: Avoid branch, check if this can be guaranteed to always be Some(T)
                        (self.buf.expect("ParserIterator.buf was None"), self.data, self.mark, self.state)
                    }
                }

                impl<I: Input, F, P, T> Iterator for ParserIterator<I, F, P, T>
                  where F: FnMut() -> P,
                        P: Parser<I> {
                    type Item = P::Output;

                    #[inline]
                    fn size_hint(&$size_hint_self) -> (usize, Option<usize>) {
                        $size_hint
                    }

                    #[inline]
                    fn next(&mut $next_self) -> Option<Self::Item> {
                        $pre_next

                        // TODO: Remove the branches here (ie. take + unwrap)
                        let i = $next_self.buf.take().expect("ParserIterator.buf was None");

                        // TODO: Any way to prevent marking here since it is not used at all times?
                        $next_self.mark = i.mark();

                        match ($next_self.parser_ctor)().parse(i) {
                            (b, Ok(v)) => {
                                $next_self.buf = Some(b);

                                $on_next

                                Some(v)
                            },
                            (b, Err(e)) => {
                                $next_self.buf   = Some(b);
                                $next_self.state = Some(e);

                                None
                            },
                        }
                    }
                }

                // TODO: Not always used
                let mark = i.mark();

                let mut iter = ParserIterator::<_, _, _, $t> {
                    state:       None,
                    parser_ctor: self.parser_ctor,
                    buf:         Some(i),
                    mark:        mark,
                    data:        self.data,
                    _i:          PhantomData,
                    _t:          PhantomData,
                    _p:          PhantomData,
                };

                let $result: T = FromIterator::from_iter(iter.by_ref());

                match iter.end_state() {
                    $($pat => $arm),*
                }
            }
        }
    }
}

/// Version of run_iter which allows for an additional parser to be run which can terminate
/// iteration early.
macro_rules! many_till_iter {
    (
        doc:         $doc:expr,
        struct_name: $name:ident,
        state:       $data_ty:ty,

        size_hint($size_hint_self:ident) $size_hint:block
        next($next_self:ident) {
            pre $pre_next:block
            on  $on_next:block
        }

        => $result:ident : $t:ty {
             $($pat:pat => $arm:expr),*$(,)*
        }
    ) => {
        #[doc=$doc]
        pub struct $name<I, F, G, P, Q, T>
          where I: Input,
                F: FnMut() -> P,
                G: FnMut() -> Q,
                P: Parser<I>,
                Q: Parser<I, Error=P::Error>,
                T: FromIterator<P::Output> {
            /// Parser constructor to repeat
            p_ctor: F,
            /// Parser constructor for the end
            q_ctor: G,
            /// Nested state
            data:   $data_ty,
            _i: PhantomData<I>,
            _p: PhantomData<P>,
            _q: PhantomData<Q>,
            _t: PhantomData<T>,
        }

        impl<I, F, G, P, Q, T> Parser<I> for $name<I, F, G, P, Q, T>
          where I: Input,
                F: FnMut() -> P,
                G: FnMut() -> Q,
                P: Parser<I>,
                Q: Parser<I, Error=P::Error>,
                T: FromIterator<P::Output> {
            type Output = T;
            type Error  = P::Error;

            #[inline]
            fn parse(self, i: I) -> (I, Result<T, P::Error>) {
                enum EndStateTill<E> {
                    Error(E),
                    Incomplete,
                    EndSuccess,
                }

                /// Iterator used by `many_till` and `many1`.
                struct ParserIterator<I, F, G, P, Q>
                  where I: Input,
                        F: FnMut() -> P,
                        G: FnMut() -> Q,
                        P: Parser<I>,
                        Q: Parser<I, Error=P::Error> {
                    /// Last state of the parser
                    state:  EndStateTill<P::Error>,
                    /// Parser to repeat
                    parser: F,
                    /// Parser to end
                    end:    G,
                    /// Remaining buffer.
                    ///
                    /// Wrapped in Option to prevent two calls to destructors.
                    buf:    Option<I>,
                    /// Nested state
                    data:   $data_ty,
                    _i: PhantomData<I>,
                    _p: PhantomData<P>,
                    _q: PhantomData<Q>,
                }

                impl<I, F, G, P, Q> ParserIterator<I, F, G, P, Q>
                  where I: Input,
                        F: FnMut() -> P,
                        G: FnMut() -> Q,
                        P: Parser<I>,
                        Q: Parser<I, Error=P::Error> {
                    /// Destructures the iterator returning the position just after the last successful parse as
                    /// well as the state of the last attempt to parse data.
                    #[inline]
                    fn end_state(self) -> (I, $data_ty, EndStateTill<P::Error>) {
                        // TODO: Avoid branch, check if this can be guaranteed to always be Some(T)
                        (self.buf.expect("Iter.buf was None"), self.data, self.state)
                    }
                }

                impl<I, F, G, P, Q> Iterator for ParserIterator<I, F, G, P, Q>
                  where I: Input,
                        F: FnMut() -> P,
                        G: FnMut() -> Q,
                        P: Parser<I>,
                        Q: Parser<I, Error=P::Error> {
                    type Item = P::Output;

                    #[inline]
                    fn size_hint(&$size_hint_self) -> (usize, Option<usize>) {
                        $size_hint
                    }

                    #[inline]
                    fn next(&mut $next_self) -> Option<Self::Item> {
                        $pre_next

                        // TODO: Remove the branches here (ie. take + unwrap)
                        let i = $next_self.buf.take().expect("Iter.buf was None");

                        match ($next_self.parser)().parse(i) {
                            (b, Ok(v)) => {
                                $next_self.buf = Some(b);

                                $on_next

                                Some(v)
                            },
                            (b, Err(e)) => {
                                $next_self.buf   = Some(b);
                                $next_self.state = EndStateTill::Error(e);

                                None
                            },
                        }
                    }
                }

                let mut iter = ParserIterator {
                    state:  EndStateTill::Incomplete,
                    parser: self.p_ctor,
                    end:    self.q_ctor,
                    buf:    Some(i),
                    data:   self.data,
                    _i:     PhantomData,
                    _p:     PhantomData,
                    _q:     PhantomData,
                };

                let $result: $t = FromIterator::from_iter(iter.by_ref());

                match iter.end_state() {
                    $($pat => $arm),*
                }
            }
        }
    }
}

/// Used in `many_till_iter!` macro to attempt to end iteration early. If the test succeeds the
/// buffer position will be updated and the state set to `EndStateTill::EndSuccess` and a `None`
/// will be returned, stopping the iteration. If the test fails execution continues.
macro_rules! iter_till_end_test {
    ( $the_self:ident ) => { {
        // TODO: Remove the branches here (ie. take + unwrap)
        let i = $the_self.buf.take().expect("Iter.buf was None");
        let m = i.mark();

        match ($the_self.end)().parse(i) {
            (b, Ok(_)) => {
                $the_self.buf   = Some(b);
                $the_self.state = EndStateTill::EndSuccess;

                return None
            },
            // Failed to end, restore and continue
            (b, Err(_))      => $the_self.buf = Some(b.restore(m)),
        }
    } }
}
