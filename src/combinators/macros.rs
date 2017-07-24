macro_rules! many_iter {
    (
        $(#[$attr:meta])*
        pub struct $name:ident {
            state: $data_ty:ty,

            size_hint($size_hint_self:ident) $size_hint:block
            next($next_self:ident) {
                pre $pre_next:block
                on  $on_next:block
            }
            finally($result:ident) {
                 $($pat:pat => $arm:expr),*$(,)*
            }
        }
    ) => {
        $(#[$attr])*
        pub struct $name<I, F, T>
          where I: Input,
                F: ParserConstructor<I>,
                T: FromIterator<<F::Parser as Parser<I>>::Output> {
            /// Parser to execute once for each iteration
            parser_ctor: F,
            /// Nested state
            data:      $data_ty,
            _i:        PhantomData<I>,
            _t:        PhantomData<T>,
        }

        impl<I, F, T> Parser<I> for $name<I, F, T>
          where I: Input,
                F: ParserConstructor<I>,
                T: FromIterator<<F::Parser as Parser<I>>::Output> {
            type Output = T;
            type Error  = <F::Parser as Parser<I>>::Error;

            #[inline]
            fn parse(self, i: I) -> (I, Result<T, <F::Parser as Parser<I>>::Error>) {
                /// Iterator used to run the parser multiple times
                struct ParserIterator<I: Input, F>
                  where F: ParserConstructor<I> {
                    /// Last state of the parser
                    state:  Option<<F::Parser as Parser<I>>::Error>,
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
                }

                impl<I: Input, F> ParserIterator<I, F>
                  where F: ParserConstructor<I> {
                    #[inline]
                    fn end_state(self) -> (I, $data_ty, I::Marker, Option<<F::Parser as Parser<I>>::Error>) {
                        // TODO: Avoid branch, check if this can be guaranteed to always be Some(T)
                        (self.buf.expect("ParserIterator.buf was None"), self.data, self.mark, self.state)
                    }
                }

                impl<I: Input, F> Iterator for ParserIterator<I, F>
                  where F: ParserConstructor<I> {
                    type Item = <F::Parser as Parser<I>>::Output;

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

                        match ($next_self.parser_ctor).new_parser().parse(i) {
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

                let mut iter = ParserIterator {
                    state:       None,
                    parser_ctor: self.parser_ctor,
                    buf:         Some(i),
                    mark:        mark,
                    data:        self.data,
                    _i:          PhantomData,
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
        $(#[$attr:meta])*
        pub struct $name:ident {
            state:       $data_ty:ty,

            size_hint($size_hint_self:ident) $size_hint:block
            next($next_self:ident) {
                pre $pre_next:block
                on  $on_next:block
            }
            finally($result:ident) {
                 $($pat:pat => $arm:expr),*$(,)*
            }
        }
    ) => {
        $(#[$attr])*
        pub struct $name<I, F, G, T>
          where I: Input,
                F: ParserConstructor<I>,
                G: ParserConstructor<I>,
                G::Parser: Parser<I, Error=<F::Parser as Parser<I>>::Error>,
                T: FromIterator<<F::Parser as Parser<I>>::Output> {
            /// Parser constructor to repeat
            p_ctor: F,
            /// Parser constructor for the end
            q_ctor: G,
            /// Nested state
            data:   $data_ty,
            _i: PhantomData<I>,
            _t: PhantomData<T>,
        }

        impl<I, F, G, T> Parser<I> for $name<I, F, G, T>
          where I: Input,
                F: ParserConstructor<I>,
                G: ParserConstructor<I>,
                G::Parser: Parser<I, Error=<F::Parser as Parser<I>>::Error>,
                T: FromIterator<<F::Parser as Parser<I>>::Output> {
            type Output = T;
            type Error  = <F::Parser as Parser<I>>::Error;

            #[inline]
            fn parse(self, i: I) -> (I, Result<T, <F::Parser as Parser<I>>::Error>) {
                enum EndStateTill<E> {
                    Error(E),
                    Incomplete,
                    EndSuccess,
                }

                /// Iterator used by `many_till` and `many1`.
                struct ParserIterator<I, F, G>
                  where I: Input,
                        F: ParserConstructor<I>,
                        G: ParserConstructor<I>,
                        G::Parser: Parser<I, Error=<F::Parser as Parser<I>>::Error> {
                    /// Last state of the parser
                    state:  EndStateTill<<F::Parser as Parser<I>>::Error>,
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
                }

                impl<I, F, G> ParserIterator<I, F, G>
                  where I: Input,
                        F: ParserConstructor<I>,
                        G: ParserConstructor<I>,
                        G::Parser: Parser<I, Error=<F::Parser as Parser<I>>::Error> {
                    /// Destructures the iterator returning the position just after the last successful parse as
                    /// well as the state of the last attempt to parse data.
                    #[inline]
                    fn end_state(self) -> (I, $data_ty, EndStateTill<<F::Parser as Parser<I>>::Error>) {
                        // TODO: Avoid branch, check if this can be guaranteed to always be Some(T)
                        (self.buf.expect("Iter.buf was None"), self.data, self.state)
                    }
                }

                impl<I, F, G> Iterator for ParserIterator<I, F, G>
                  where I: Input,
                        F: ParserConstructor<I>,
                        G: ParserConstructor<I>,
                        G::Parser: Parser<I, Error=<F::Parser as Parser<I>>::Error> {
                    type Item = <F::Parser as Parser<I>>::Output;

                    #[inline]
                    fn size_hint(&$size_hint_self) -> (usize, Option<usize>) {
                        $size_hint
                    }

                    #[inline]
                    fn next(&mut $next_self) -> Option<Self::Item> {
                        $pre_next

                        // TODO: Remove the branches here (ie. take + unwrap)
                        let i = $next_self.buf.take().expect("Iter.buf was None");

                        match ($next_self.parser).new_parser().parse(i) {
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
                };

                let $result: T = FromIterator::from_iter(iter.by_ref());

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
///
/// NOTE: Only use if ending is optional.
///
/// TODO: Remove and incorporate in the other items.
macro_rules! iter_till_end_test {
    ( $the_self:ident ) => { {
        // TODO: Remove the branches here (ie. take + unwrap)
        let i = $the_self.buf.take().expect("Iter.buf was None");
        let m = i.mark();

        match ($the_self.end).new_parser().parse(i) {
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
