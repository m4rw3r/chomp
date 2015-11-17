/// Macro emulating `do`-notation for the parser monad, automatically threading the linear type.
/// 
/// ```ignore
/// parse!{input;
///                 parser("parameter");
///     let value = other_parser();
///     
///     ret do_something(value);
/// }
/// // equivalent to:
/// parser(input, "parameter").bind(|i, _|
///     other_parser(i).bind(|i, value|
///         i.ret(do_something(value))))
/// ```
/// 
/// # Example
/// 
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::{Input, ParseResult, Error};
/// use chomp::{take_while1, token};
///
/// let i = Input::new("martin wernstål\n".as_bytes());
/// 
/// #[derive(Debug, Eq, PartialEq)]
/// struct Name<'a> {
///     first: &'a [u8],
///     last:  &'a [u8],
/// }
/// 
/// let r = parse!{i;
///     let first = take_while1(|c| c != b' ');
///                 token(b' ');
///     let last  = take_while1(|c| c != b'\n');
///
///     ret @ _, Error<_>: Name{
///         first: first,
///         last:  last,
///     }
/// };
/// 
/// assert_eq!(r.unwrap(), Name{first: b"martin", last: "wernstål".as_bytes()});
/// # }
/// ```
/// 
/// ## Grammar
/// 
/// EBNF using `$ty`, `$expr`, `$ident` and `$pat` for the equivalent Rust macro patterns.
/// 
/// ```text
/// RET_TYPED     = '@' $ty ',' $ty ':' $expr
/// RET_PLAIN     = $expr
///
/// ERR_TYPED     = '@' $ty ',' $ty ':' $expr
/// ERR_PLAIN     = $expr
///
/// VAR           = $ident ':' $ty | $pat
/// ACTION        = INLINE_ACTION | NAMED_ACTION
/// INLINE_ACTION = $ident '->' $expr
/// NAMED_ACTION  = $ident '(' ($expr ',')* ','? ')'
/// 
/// BIND          = 'let' VAR '=' ACTION
/// THEN          = ACTION
///
/// RET           = 'ret' ( RET_TYPED | RET_PLAIN )
/// ERR           = 'err' ( ERR_TYPED | ERR_PLAIN )
/// 
/// EXPR          = ( BIND ';' | THEN ';' )* (RET | ERR | THEN)
/// ```
#[macro_export]
macro_rules! parse {
    ( $($t:tt)* ) => { __parse_internal!{ $($t)* } };
}

/// Actual implementation of the parse macro, hidden to make the documentation easier to read.
#[macro_export]
#[doc(hidden)]
macro_rules! __parse_internal {
    // RET_TYPED     = '@' $ty ',' $ty ':' $expr
    ( @RET($i:expr); @ $t_ty:ty , $e_ty:ty : $e:expr ) => { $i.ret::<$t_ty, $e_ty>($e) };

    // RET_PLAIN     = $expr
    ( @RET($i:expr); $e:expr ) => { $i.ret($e) };

    // ERR_TYPED     = '@' $ty ',' $ty ':' $expr
    ( @ERR($i:expr); @ $t_ty:ty , $e_ty:ty : $e:expr ) => { $i.err::<$t_ty, $e_ty>($e) };

    // ERR_PLAIN     = $expr
    ( @ERR($i:expr); $e:expr ) => { $i.err($e) };

    // VAR           = $ident ':' $ty | $pat
    // pattern must be before ident
    ( @BIND($i:expr); $v:pat              = $($t:tt)* ) => { __parse_internal!{ @ACTION($i, $v      ); $($t)* } };
    ( @BIND($i:expr); $v:ident : $v_ty:ty = $($t:tt)* ) => { __parse_internal!{ @ACTION($i, $v:$v_ty); $($t)* } };

    // ACTION        = INLINE_ACTION | NAMED_ACTION

    // INLINE_ACTION = $ident '->' $expr
    // version with expression following, nonterminal:
    ( @ACTION($i:expr, $($v:tt)*); $m:ident -> $e:expr ; $($t:tt)*) => { __parse_internal!{ @CONCAT({ let $m = $i; $e }, $($v)*); $($t)* } };
    // terminal:
    ( @ACTION($i:expr, $($v:tt)*); $m:ident -> $e:expr )            => { { let $m = $i; $e } };

    // NAMED_ACTION  = $ident '(' ($expr ',')* ','? ')'
    // version with expression following, nonterminal:
    ( @ACTION($i:expr, $($v:tt)*); $f:ident ( $($p:expr),* $(,)*) ; $($t:tt)* ) => { __parse_internal!{ @CONCAT($f($i, $($p),*), $($v)*); $($t)*} };
    // terminal:
    ( @ACTION($i:expr, $($v:tt)*); $f:ident ( $($p:expr),* $(,)*) )             => { $f($i, $($p),*) };

    // Ties an expression together with the next, using the bind operator
    // invoked from @ACTION and @BIND (via @ACTION)
    // three variants are needed to coerce the tt-list into a parameter token
    // an additional three variants are needed to handle tailing semicolons, if there is nothing
    // else to expand, do not use bind
    ( @CONCAT($i:expr, _                  );              ) => { $i };
    ( @CONCAT($i:expr, _                  ); $($tail:tt)+ ) => { $i.bind(|i, _|        __parse_internal!{ i; $($tail)* }) };
    ( @CONCAT($i:expr, $v:pat             );              ) => { $i };
    ( @CONCAT($i:expr, $v:pat             ); $($tail:tt)+ ) => { $i.bind(|i, $v|       __parse_internal!{ i; $($tail)* }) };
    ( @CONCAT($i:expr, $v:ident : $v_ty:ty);              ) => { $i };
    ( @CONCAT($i:expr, $v:ident : $v_ty:ty); $($tail:tt)+ ) => { $i.bind(|i, $v:$v_ty| __parse_internal!{ i; $($tail)* }) };

    // EXPR          = ( BIND ';' | THEN ';' )* (RET | ERR | THEN)
    // TODO: Any way to prevent BIND from being the last?

    // BIND          = 'let' VAR '=' ACTION
    ( $i:expr ; let $($tail:tt)* ) => { __parse_internal!{ @BIND($i); $($tail)+ } };
    // RET           = 'ret' ( RET_TYPED | RET_PLAIN )
    ( $i:expr ; ret $($tail:tt)+ ) => { __parse_internal!{ @RET($i); $($tail)+ } };
    // ERR           = 'err' ( ERR_TYPED | ERR_PLAIN )
    ( $i:expr ; err $($tail:tt)+ ) => { __parse_internal!{ @ERR($i); $($tail)+ } };
    // THEN          = ACTION
    // needs to be last since it is the most general
    ( $i:expr ; $($tail:tt)+ )     => { __parse_internal!{ @ACTION($i, _); $($tail)+ } };

    // Terminals:
    ( $i:expr ; ) => { $i };
    ( $i:expr )   => { $i };
}

#[cfg(test)]
mod test {
    /// Simplified implementation of the emulated monad using linear types.
    #[derive(Debug, Eq, PartialEq)]
    struct Input(i64);
    /// Simplified implementation of the emulated monad using linear types.
    #[derive(Debug, Eq, PartialEq)]
    enum Data<T, E> {
        Value(i64, T),
        Error(i64, E),
    }

    impl Input {
        fn ret<T, E>(self, t: T) -> Data<T, E> {
            Data::Value(self.0, t)
        }

        fn err<T, E>(self, e: E) -> Data<T, E> {
            Data::Error(self.0, e)
        }
    }

    impl<T, E> Data<T, E> {
        fn bind<F, U, V = E>(self, f: F) -> Data<U, V>
          where F: FnOnce(Input, T) -> Data<U, V>,
                V: From<E> {
            match self {
                Data::Value(i, t) => f(Input(i), t).map_err(From::from),
                Data::Error(i, e) => Data::Error(i, From::from(e)),
            }
        }

        fn map_err<F, V>(self, f: F) -> Data<T, V>
          where F: FnOnce(E) -> V {
            match self {
                Data::Value(i, t) => Data::Value(i, t),
                Data::Error(i, e) => Data::Error(i, f(e)),
            }
        }
    }

    #[test]
    fn empty() {
        let i = 123;

        let r = parse!{i};

        assert_eq!(r, 123);
    }

    #[test]
    fn empty_expr() {
        let r = parse!{1 + 2};

        assert_eq!(r, 3);
    }

    #[test]
    fn ret() {
        let i = Input(123);

        // Type annotation necessary since ret leaves E free
        let r: Data<_, ()> = parse!{i; ret "foo"};

        assert_eq!(r, Data::Value(123, "foo"));
    }

    #[test]
    fn ret_typed() {
        let i = Input(123);

        let r = parse!{i; ret @ _, (): "foo"};

        assert_eq!(r, Data::Value(123, "foo"));
    }

    #[test]
    fn ret_typed2() {
        let i = Input(123);

        let r = parse!{i; ret @ &str, (): "foo"};

        assert_eq!(r, Data::Value(123, "foo"));
    }

    #[test]
    fn err() {
        let i = Input(123);

        // Type annotation necessary since err leaves T free
        let r: Data<(), _> = parse!{i; err "foo"};

        assert_eq!(r, Data::Error(123, "foo"));
    }

    #[test]
    fn err_typed() {
        let i = Input(123);

        let r = parse!{i; err @(), _: "foo"};

        assert_eq!(r, Data::Error(123, "foo"));
    }

    #[test]
    fn err_typed2() {
        let i = Input(123);

        let r = parse!{i; err @(), &str: "foo"};

        assert_eq!(r, Data::Error(123, "foo"));
    }

    #[test]
    fn action() {
        fn doit(i: Input) -> Data<&'static str, ()> {
            Data::Value(i.0, "doit")
        }

        let i = Input(123);

        let r = parse!(i; doit());

        assert_eq!(r, Data::Value(123, "doit"));
    }

    #[test]
    fn action2() {
        fn doit(i: Input, p: &str) -> Data<&str, ()> {
            Data::Value(i.0, p)
        }

        let i = Input(123);

        let r = parse!(i; doit("doit"));

        assert_eq!(r, Data::Value(123, "doit"));
    }

    #[test]
    fn action3() {
        fn doit(i: Input, p: &str, u: u32) -> Data<(&str, u32), ()> {
            Data::Value(i.0, (p, u))
        }

        let i = Input(123);

        let r = parse!(i; doit("doit", 1337));

        assert_eq!(r, Data::Value(123, ("doit", 1337)));
    }

    #[test]
    fn two_actions() {
        fn doit(i: Input) -> Data<u32, ()> {
            assert_eq!(i.0, 123);

            Data::Value(321, 1)
        }
        fn something(i: Input) -> Data<u32, ()> {
            assert_eq!(i.0, 321);

            Data::Value(123, 2)
        }

        let i = Input(123);

        let r = parse!(i; doit(); something());

        assert_eq!(r, Data::Value(123, 2));
    }

    #[test]
    fn two_actions2() {
        fn doit(i: Input, n: u32) -> Data<u32, ()> {
            assert_eq!(i.0, 123);

            Data::Value(321, n)
        }
        fn something(i: Input, n: u32) -> Data<u32, ()> {
            assert_eq!(i.0, 321);

            Data::Value(123, n)
        }

        let i = Input(123);

        let r = parse!(i; doit(22); something(33));

        assert_eq!(r, Data::Value(123, 33));
    }

    #[test]
    fn two_actions3() {
        fn doit(i: Input, n: u32, x: i32) -> Data<(u32, i32), ()> {
            assert_eq!(i.0, 123);

            Data::Value(321, (n, x))
        }
        fn something(i: Input, n: u32, x: i32) -> Data<(u32, i32), ()> {
            assert_eq!(i.0, 321);

            Data::Value(123, (n, x))
        }

        let i = Input(123);

        let r = parse!(i; doit(22, 1); something(33, 2));

        assert_eq!(r, Data::Value(123, (33, 2)));
    }

    #[test]
    fn tailing_semicolon() {
        fn f(n: u32) -> u32 {
            n + 3
        }

        let r = parse!{123; f(); };

        assert_eq!(r, 126);
    }
}
