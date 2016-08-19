/// Macro emulating `do`-notation for the parser monad, automatically threading the linear type.
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::prelude::*;
/// # fn parser<I: Input>(i: I, _s: &str) -> ParseResult<I, (), ()> { i.ret(()) }
/// # fn other_parser<I: Input>(i: I) -> ParseResult<I, u8, ()> { i.ret(23) }
/// # fn do_something(_i: u8) -> u32 { 23 }
/// # let input = &b"foo"[..];
/// # let _r: ParseResult<_, _, ()> =
/// parse!{input;
///                 parser("parameter");
///     let value = other_parser();
///
///     ret do_something(value)
/// }
/// # ;
/// # let _r: ParseResult<_, _, ()> =
/// // is equivalent to:
/// parser(input, "parameter").bind(|i, _|
///     other_parser(i).bind(|i, value|
///         i.ret(do_something(value))))
/// # ;
/// # }
/// ```
///
/// # Examples
///
/// Parsing into a struct using the basic provided parsers:
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::prelude::{Buffer, Error, Input, ParseResult, parse_only, take_while1, token};
///
/// #[derive(Debug, Eq, PartialEq)]
/// struct Name<B: Buffer> {
///     first: B,
///     last:  B,
/// }
///
/// fn parser<I: Input<Token=u8>>(i: I) -> ParseResult<I, Name<I::Buffer>, Error<I::Token>> {
///     parse!{i;
///         let first = take_while1(|c| c != b' ');
///                     token(b' ');
///         let last  = take_while1(|c| c != b'\n');
///
///         ret @ _, Error<u8>: Name{
///             first: first,
///             last:  last,
///         }
///     }
/// }
///
/// assert_eq!(parse_only(parser, "Martin Wernstål\n".as_bytes()), Ok(Name{
///     first: &b"Martin"[..],
///     last: "Wernstål".as_bytes()
/// }));
/// # }
/// ```
///
/// Parsing an IP-address with a string-prefix and terminated with semicolon using the `<*` (skip)
/// operator to make it more succint:
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::prelude::{U8Input, Input, SimpleResult, parse_only, string, token};
/// use chomp::ascii::decimal;
///
/// fn parse_ip<I: U8Input>(i: I) -> SimpleResult<I, (u8, u8, u8, u8)> {
///     parse!{i;
///                 string(b"ip:");
///         let a = decimal() <* token(b'.');
///         let b = decimal() <* token(b'.');
///         let c = decimal() <* token(b'.');
///         let d = decimal();
///                 token(b';');
///         ret (a, b, c, d)
///     }
/// }
///
/// assert_eq!(parse_only(parse_ip, b"ip:192.168.0.1;"), Ok((192, 168, 0, 1)));
/// # }
/// ```
///
/// Parsing a log-level using the `<|>` alternation (or) operator:
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::prelude::{parse_only, string};
///
/// #[derive(Debug, Eq, PartialEq)]
/// enum Log {
///     Error,
///     Warning,
///     Info,
///     Debug,
/// };
///
/// let level        = |i, b, r| string(i, b).map(|_| r);
/// let log_severity = parser!{
///     level(b"ERROR", Log::Error)   <|>
///     level(b"WARN",  Log::Warning) <|>
///     level(b"INFO",  Log::Info)    <|>
///     level(b"DEBUG", Log::Debug)
/// };
///
/// assert_eq!(parse_only(log_severity, b"INFO"), Ok(Log::Info));
/// # }
/// ```
///
/// # Grammar
///
/// EBNF using `$ty`, `$expr`, `$ident` and `$pat` for the equivalent Rust macro patterns.
///
/// ```text
/// Block     ::= Statement* Expr
/// Statement ::= Bind ';'
///             | Expr ';'
/// Bind      ::= 'let' Var '=' Expr
/// Var       ::= $pat
///             | $ident ':' $ty
///
/// /* Expr is split this way to allow for operator precedence */
/// Expr      ::= ExprAlt
///             | ExprAlt   ">>" Expr
/// ExprAlt   ::= ExprSkip
///             | ExprSkip "<|>" ExprAlt
/// ExprSkip  ::= Term
///             | Term     "<*" ExprSkip
///
/// Term      ::= Ret
///             | Err
///             | '(' Expr ')'
///             | Inline
///             | Named
///
/// Ret       ::= "ret" Typed
///             | "ret" $expr
/// Err       ::= "err" Typed
///             | "err" $expr
/// Typed     ::= '@' $ty ',' $ty ':' $expr
/// Inline    ::= $ident "->" $expr
/// Named     ::= $ident '(' ($expr ',')* (',')* ')'
/// ```
///
/// ## Statement
///
/// A statement is a line ending in a semicolon. This must be followed by either another statement
/// or by an expression which ends the block.
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::ascii::decimal;
/// # use chomp::prelude::{parse_only, U8Input, Input, token, SimpleResult};
/// # fn my_parser<I: U8Input>(i: I) -> SimpleResult<I, u32> {
/// parse!{i;
///     token(b':');
///     let n: u32 = decimal();
///     ret n * 2
/// }
/// # }
/// # assert_eq!(parse_only(my_parser, b":21"), Ok(42));
/// # }
/// ```
///
/// ### Bind
///
/// A bind statement uses a `let`-binding to bind a value of a parser-expression within the parsing
/// context. The expression to the right of the equal-sign will be evaluated and if the parser is
/// still in a success state the value will be bound to the pattern following `let`.
///
/// The patter can either just be an identifier but it can also be any irrefutable match-pattern,
/// types can also be declared with `identifier: type` when necessary (eg. declare integer type
/// used with the `decimal` parser).
///
/// ### Action
///
/// An action is any parser-expression, ended with a semicolon. This will be executed and its
/// result will be discarded before proceeding to the next statement or the ending expression.
/// Any error will exit early and will be propagated.
///
/// ## Expression
///
/// A parser expression can either be the only part of a `parse!` macro (eg. for alternating as
/// seen above) or it can be a part of a bind or action statement or it is the final result of a
/// parse-block.
///
/// ### Named
///
/// A named action is like a function call, but will be expanded to include the parsing context
/// (`Input`) as the first parameter. The syntax is currently limited to a rust identifier followed
/// by a parameter list within parentheses. The parentheses are mandatory.
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::prelude::{parse_only, U8Input, SimpleResult};
/// # fn my_parser<I: U8Input>(i: I) -> SimpleResult<I, &'static str> {
/// fn do_it<'a, I: U8Input>(i: I, s: &'a str) -> SimpleResult<I, &'a str> { i.ret(s) }
///
/// parse!{i;
///     do_it("second parameter")
/// }
/// # }
/// # assert_eq!(parse_only(my_parser, b":21"), Ok("second parameter"));
/// # }
/// ```
///
/// ### Ret and Err
///
/// Many times you want to move a value into the parser monad, eg. to return a result or report an
/// error. The `ret` and `err` keywords provide this functionality inside of `parse!`-expressions.
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::prelude::{parse_only, Input};
/// let r: Result<_, (_, ())> = parse_only(
///     parser!{ ret "some success data" },
///     b"input data"
/// );
///
/// assert_eq!(r, Ok("some success data"));
/// # }
/// ```
///
/// In the example above the `Result<_, (_, ())>` type-annotation is required since `ret`
/// leaves the error type `E` free which means that the `parser!` expression above cannot infer the
/// error type without the annotation. `ret` and `end` both provide a mechanism to supply this
/// information inline:
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::prelude::{parse_only, Input};
/// let r = parse_only(parser!{ err @ u32, _: "some error data" }, b"input data");
///
/// assert_eq!(r, Err((&b"input data"[..], "some error data")));
/// # }
/// ```
///
/// Note that we only declare the success type (`u32` above) and leave out the type of the error
/// (by using `_`) since that can be uniquely inferred.
///
/// ### Inline
///
/// An inline expression is essentially a closure where the parser state (`Input` type) is exposed.
/// This is useful for doing eg. inline `match` statements or to delegate to another parser which
/// requires some plain Rust logic:
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::prelude::{parse_only, Input, ParseResult};
/// fn other_parser<I: Input>(i: I) -> ParseResult<I, &'static str, &'static str> {
///     i.ret("Success!")
/// }
///
/// let condition = true;
///
/// let p = parser!{
///     state -> match condition {
///         true  => other_parser(state),
///         false => Input::err(state, "failure"),
///     }
/// };
///
/// assert_eq!(parse_only(p, b""), Ok("Success!"));
/// # }
/// ```
///
/// ### Operators
///
/// Expressions also supports using operators in between sub-expressions to make common actions
/// more succint. These are infix operators with right associativity (ie. they are placed
/// between expression terms and are grouped towards the right). The result of the expression as a
/// whole will be deiced by the operator.
///
/// Ordered after operator precedence:
///
/// 1. `<*`, skip
///
///    Evaluates the parser to the left first and on success evaluates the parser on the right,
///    skipping its result.
///
///    ```
///    # #[macro_use] extern crate chomp;
///    # fn main() {
///    # use chomp::ascii::decimal; use chomp::prelude::{parse_only, token};
///    let p = parser!{ decimal() <* token(b';') };
///
///    assert_eq!(parse_only(p, b"123;"), Ok(123u32));
///    # }
///    ```
///
/// 2. `<|>`, or
///
///    Attempts to evaluate the parser on the left and if that fails it will backtrack and retry
///    with the parser on the right. Is equivalent to stacking `or` combinators.
///
///    ```
///    # #[macro_use] extern crate chomp;
///    # fn main() {
///    # use chomp::prelude::{parse_only, token};
///    let p = parser!{ token(b'a') <|> token(b'b') };
///
///    assert_eq!(parse_only(p, b"b"), Ok(b'b'));
///    # }
///    ```
///
/// 3. `>>`, then
///
///    Evaluates the parser to the left, then throws away any value and evaluates the parser on
///    the right.
///
///    ```
///    # #[macro_use] extern crate chomp;
///    # fn main() {
///    # use chomp::prelude::{parse_only, token};
///    let p = parser!{ token(b'a') >> token(b';') };
///
///    assert_eq!(parse_only(p, b"a;"), Ok(b';'));
///    # }
///    ```
///
/// These operators correspond to the equivalent operators found in Haskell's `Alternative`,
/// `Applicative` and `Monad` typeclasses, with the exception of being right-associative (the
/// operators are left-associative in Haskell).
///
/// An Inline expression needs to be wrapped in parenthesis to parse (`$expr` pattern in macros
/// require `;` or `,` to be terminated at the same nesting level):
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::prelude::{Input, parse_only};
/// let p = parser!{ (i -> Input::err(i, "foo")) <|> (i -> Input::ret(i, "bar")) };
///
/// assert_eq!(parse_only(p, b"a;"), Ok("bar"));
/// # }
/// ```
///
/// # Debugging
///
/// Errors in Rust macros can be hard to decipher at times, especially when using very complex
/// macros which incrementally parse their input. This section is provided to give some hints and
/// solutions for common problems. If this still does not solve the problem, feel free to ask
/// questions on GitHub or via email or open an issue.
///
/// ## Macro recursion limit
///
/// The `parse!` macro is expanding by recursively invoking itself, parsing a bit of the input each
/// iteration. This sometimes reaches the recursion-limit for macros in Rust:
///
/// ```text
/// src/macros.rs:439:99: 439:148 error: recursion limit reached while expanding the macro `__parse_internal`
/// src/macros.rs:439     ( @EXPR_SKIP($input:expr; $($lhs:tt)*) $t1:tt $t2:tt )                                   => { __parse_internal!{@TERM($input) $($lhs)* $t1 $t2} };
/// ```
///
/// The default recursion limit is `64`, this can be raised by using a crate-annotation in the
/// crate where the recursion limit is an issue:
///
/// ```
/// #![recursion_limit="100"]
/// ```
///
/// # Debugging macro expansion
///
/// If you are using the nightly version of rust you can use the feature `trace_macros` to see how
/// the macro is expanded:
///
/// ```ignore
/// #![feature(trace_macros)]
///
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// trace_macros!(true);
/// let p = parser!{ decimal() <* token(b';') };
/// trace_macros!(false);
/// # }
/// ```
///
/// This will result in a printout similar to this:
///
/// ```text
/// parser! { decimal (  ) < * token ( b';' ) }
/// parse! { i ; decimal (  ) < * token ( b';' ) }
/// __parse_internal! { i ; decimal (  ) < * token ( b';' ) }
/// __parse_internal! { @ STATEMENT ( ( i ; _ ) ) decimal (  ) < * token ( b';' ) }
/// __parse_internal! { @ BIND ( ( i ; _ ) decimal (  ) < * token ( b';' ) ) }
/// __parse_internal! { @ EXPR ( i ; ) decimal (  ) < * token ( b';' ) }
/// __parse_internal! { @ EXPR_ALT ( i ; ) decimal (  ) < * token ( b';' ) }
/// __parse_internal! { @ EXPR_SKIP ( i ; ) decimal (  ) < * token ( b';' ) }
/// __parse_internal! { @ TERM ( i ) decimal (  ) }
/// __parse_internal! { @ EXPR_SKIP ( i ; ) token ( b';' ) }
/// __parse_internal! { @ TERM ( i ) token ( b';' ) }
/// ```
///
/// Output like the above can make it clearer where it is actually failing, and can sometimes
/// highlight the exact problem (with the help of looking at the grammar found above).
///
/// ## Function error pointing to macro code
///
/// Sometimes non-syntax errors will occur in macro code, `rustc` currently (on stable) has issues
/// with actually displaying the actual code which causes the problem. Instead the macro-part will
/// be highlighted as the cause of the issue:
///
/// ```text
/// src/macros.rs:431:71: 431:97 error: this function takes 1 parameter but 2 parameters were supplied [E0061]
/// src/macros.rs:431     ( @TERM($input:expr) $func:ident ( $($param:expr),* $(,)*) ) => { $func($input, $($param),*) };
///                                                                                         ^~~~~~~~~~~~~~~~~~~~~~~~~~
/// src/macros.rs:489:99: 489:148 note: in this expansion of __parse_internal! (defined in src/macros.rs)
/// ...
/// ```
///
/// Usually this is related to a Named expression which is used to invoke a function, but the
/// function-parameters do not match the expected. Check all the named invocations in the
/// macro-invocation and keep in mind that the first parameter will be an `Input<I>` which is added
/// automatically. If that still does not help, try using nighly and the `trace_macro` feature to
/// see what is expanded.
///
/// ## `error: expected ident, found foo`
///
/// This error (with `foo` being a user-defined symbol)  can be caused by having a Bind statement
/// as the last statement in a `parse!` block.  The last part of a `parse!` block must be an
/// expression.
///
/// ```text
/// src/macros.rs:551:111: 551:116 error: expected ident, found foo
/// src/macros.rs:551     ( $input:expr ; let $name:pat = $($tail:tt)+ )
///     => { __parse_internal!{@STATEMENT(($input; $name)) $($tail)+} };
///                                                ^~~~~
/// ```
#[macro_export]
macro_rules! parse {
    ( $($t:tt)* ) => { __parse_internal!{ $($t)* } };
}

// FIXME: Update the grammar

/// Internal rule to create an or-combinator, separate macro so that tests can override it.
///
/// Cannot make a method on `Input` due to type-inference failures due to the exact implementation
/// of `or` not being fully specified.
#[macro_export]
#[doc(hidden)]
macro_rules! __parse_internal_or {
    ($lhs:expr, $rhs:expr) => { $crate::combinators::or($lhs, $rhs) };
}

/// Actual implementation of the parse macro, hidden to make the documentation easier to read.
///
/// Patterns starting with @ symbols are internal rules, used by other parts of the macro.
#[macro_export]
#[doc(hidden)]
macro_rules! __parse_internal {
    // Internal rules:

    // BIND ties an expression together with the following statement
    // The four versions are needed to allow the empty case (no tailing allowed on the empty
    // case), _, $pat and $ident:$ty.
    ( @BIND((_)                         $($exp:tt)+) )              => {  __parse_internal!{@EXPR() $($exp)* } };
    ( @BIND((_)                         $($exp:tt)+) $($tail:tt)+ ) => { bind(__parse_internal!{@EXPR() $($exp)* }, |_| __parse_internal!{$($tail)* }) };
    ( @BIND(($name:pat)                 $($exp:tt)+) $($tail:tt)+ ) => { bind(__parse_internal!{@EXPR() $($exp)* }, |$name| __parse_internal!{$($tail)* }) };
    ( @BIND(($name:ident : $name_ty:ty) $($exp:tt)+) $($tail:tt)+ ) => { bind(__parse_internal!{@EXPR() $($exp)* }, |$name : $name_ty| __parse_internal!{$($tail)* }) };

    // Term ::= Ret
    //        | Err
    //        | '(' Expr ')'
    //        | Inline
    //        | Named
    // Ret ::= "ret" Typed
    ( @TERM(ret @ $t_ty:ty , $e_ty:ty : $e:expr) )   => { ret::<_, $t_ty, $e_ty>($e) };
    //       | "ret" $expr
    ( @TERM(ret $e:expr) )                           => { ret($e) };
    // Err ::= "err" Typed
    ( @TERM(err @ $t_ty:ty , $e_ty:ty : $e:expr) )   => { err::<_, $t_ty, $e_ty>($e) };
    //       | "err" $expr
    ( @TERM(err $e:expr) )                           => { err($e) };
    // '(' Expr ')'
    ( @TERM(( $($inner:tt)* )) )                     => { __parse_internal!{@EXPR() $($inner)*} };
    // Inline ::= $ident "->" $expr
    //( @TERM() $state:ident -> $e:expr )               => { { let $state = $input; $e } };
    // Named ::= $ident '(' ($expr ',')* (',')* ')'
    //( @TERM() $func:ident ( $($param:expr),* $(,)*) ) => { $func($($param),*) };
    //( @TERM($parser:expr) )                          => { $parser };

    ( @TERM($($t:tt)*) ) => { $($t)* };

    // EXPR groups by lowest priority item first which is then ">>"
    // Expr ::= ExprAlt
    ( @EXPR($($lhs:tt)*) )                          => { __parse_internal!{@EXPR_ALT() $($lhs)*} };
    //        | ExprAlt ">>" Expr
    ( @EXPR($($lhs:tt)*) >> $($tail:tt)* )          => { bind(__parse_internal!{@EXPR_ALT() $($lhs)*}, |_| __parse_internal!{@EXPR() $($tail)*}) };
    // recurse until >> or end
    // unrolled:
    // ( @EXPR($($lhs:tt)*) $t1:tt $($tail:tt)* )      => { __parse_internal!{@EXPR($($lhs)* $t1) $($tail)*} };
    ( @EXPR($($lhs:tt)*) $t1:tt )                                                               => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1} };
    ( @EXPR($($lhs:tt)*) $t1:tt >> $($tail:tt)* )                                               => { bind(__parse_internal!{@EXPR_ALT() $($lhs)* $t1}, |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt )                                                        => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt >> $($tail:tt)* )                                        => { bind(__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2}, |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt )                                                 => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt >> $($tail:tt)* )                                 => { bind(__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3}, |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt )                                          => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt >> $($tail:tt)* )                          => { bind(__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4}, |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt )                                   => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt >> $($tail:tt)* )                   => { bind(__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5}, |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt )                            => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt >> $($tail:tt)* )            => { bind(__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6}, |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt )                     => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt >> $($tail:tt)* )     => { bind(__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7}, |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $($tail:tt)* ) => {  __parse_internal!{@EXPR($($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) $($tail)*} };

    // ExprAlt ::= ExprSkip
    ( @EXPR_ALT($($lhs:tt)*) )                      => { __parse_internal!{@EXPR_SKIP() $($lhs)*} };
    //           | ExprSkip <|> ExprAlt
    ( @EXPR_ALT($($lhs:tt)*) <|> $($tail:tt)* )     => { __parse_internal_or!{__parse_internal!{@EXPR_SKIP() $($lhs)*}, __parse_internal!{@EXPR_ALT() $($tail)*}} };
    // recurse until <|> or end
    // unrolled:
    // ( @EXPR_ALT($($lhs:tt)*) $t1:tt $($tail:tt)* )  => { __parse_internal!{@EXPR_ALT($($lhs)* $t1) $($tail)*} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt )                                                               => { __parse_internal!{@EXPR_SKIP() $($lhs)* $t1} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt <|> $($tail:tt)* )                                              => { __parse_internal_or!{__parse_internal!{@EXPR_SKIP() $($lhs)* $t1}, __parse_internal!{@EXPR_ALT() $($tail)*}} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt )                                                        => { __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt <|> $($tail:tt)* )                                       => { __parse_internal_or!{__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2}, __parse_internal!{@EXPR_ALT() $($tail)*}} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt )                                                 => { __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt <|> $($tail:tt)* )                                => { __parse_internal_or!{__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3}, __parse_internal!{@EXPR_ALT() $($tail)*}} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt )                                          => { __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt <|> $($tail:tt)* )                         => { __parse_internal_or!{__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4}, __parse_internal!{@EXPR_ALT() $($tail)*}} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt )                                   => { __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt <|> $($tail:tt)* )                  => { __parse_internal_or!{__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5}, __parse_internal!{@EXPR_ALT() $($tail)*}} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt )                            => { __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt <|> $($tail:tt)* )           => { __parse_internal_or!{__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6}, __parse_internal!{@EXPR_ALT() $($tail)*}} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt )                     => { __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt <|> $($tail:tt)* )    => { __parse_internal_or!{__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7}, __parse_internal!{@EXPR_ALT() $($tail)*}} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $($tail:tt)* ) => { __parse_internal!{@EXPR_ALT($($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) $($tail)*} };

    // ExprSkip ::= Term
    ( @EXPR_SKIP($($lhs:tt)*) )                     => { __parse_internal!{@TERM($($lhs)*)} };
    //            | Term <* ExprSkip
    ( @EXPR_SKIP($($lhs:tt)*) <* $($tail:tt)* )     => { __parse_internal!{@TERM($($lhs)*)}.bind(|l| __parse_internal!{@EXPR_SKIP() $($tail)*}.map(|_| l)) };
    // recurse until <* or end
    // unrolled:
    // ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $($tail:tt)* ) => { __parse_internal!{@EXPR_SKIP($($lhs)* $t1) $($tail)*} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt )                                          => { __parse_internal!{@TERM($($lhs)* $t1)} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt <* $($tail:tt)* )                          => { __parse_internal!{@TERM($($lhs)* $t1)}.bind(|i, l| __parse_internal!{@EXPR_SKIP() $($tail)*}.map(|_| l)) };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt )                                   => { __parse_internal!{@TERM($($lhs)* $t1 $t2)} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt <* $($tail:tt)* )                   => { __parse_internal!{@TERM($($lhs)* $t1 $t2)}.bind(|i, l| __parse_internal!{@EXPR_SKIP() $($tail)*}.map(|_| l)) };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt $t3:tt )                            => { __parse_internal!{@TERM($($lhs)* $t1 $t2 $t3)} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt $t3:tt <* $($tail:tt)* )            => { __parse_internal!{@TERM($($lhs)* $t1 $t2 $t3)}.bind(|i, l| __parse_internal!{@EXPR_SKIP() $($tail)*}.map(|_| l)) };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt )                     => { __parse_internal!{@TERM($($lhs)* $t1 $t2 $t3 $t4)} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt <* $($tail:tt)* )     => { __parse_internal!{@TERM($($lhs)* $t1 $t2 $t3 $t4)}.bind(|i, l| __parse_internal!{@EXPR_SKIP() $($tail)*}.map(|_| l)) };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $($tail:tt)* ) => { __parse_internal!{@EXPR_SKIP($($lhs)* $t1 $t2 $t3 $t4 $t5) $($tail)*} };

    // STATEMENT eats and groups a full parse! expression until the next ;
    ( @STATEMENT($args:tt $($data:tt)*) )                        => { __parse_internal!{@BIND($args $($data)*)} };
    ( @STATEMENT($args:tt $($data:tt)*) ; $($tail:tt)*)          => { __parse_internal!{@BIND($args $($data)*) $($tail)*} };
    // Recurse to eat until ; or end
    // Technically could just use a single pattern for this recursion:
    // ( @STATEMENT($args:tt $($data:tt)*) $t:tt $($tail:tt)* ) => { __parse_internal!{@STATEMENT($args $($data)* $t) $($tail)*} };
    // But to avoid the recursion limit somewhat we have explicit cases for up to 10 tokens before ; or end:
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt )                                                                                      => { __parse_internal!{@BIND($args $($data)* $t1)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt ; $($tail:tt)* )                                                                       => { __parse_internal!{@BIND($args $($data)* $t1) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt )                                                                               => { __parse_internal!{@BIND($args $($data)* $t1 $t2)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt ; $($tail:tt)* )                                                                => { __parse_internal!{@BIND($args $($data)* $t1 $t2) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt )                                                                        => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt ; $($tail:tt)* )                                                         => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt )                                                                 => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt ; $($tail:tt)* )                                                  => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt )                                                          => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt ; $($tail:tt)* )                                           => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt )                                                   => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt ; $($tail:tt)* )                                    => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt )                                            => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6 $t7)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt ; $($tail:tt)* )                             => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6 $t7) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt )                                     => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt ; $($tail:tt)* )                      => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt )                              => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8 $t9)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt ; $($tail:tt)* )               => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8 $t9) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt )                      => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8 $t9 $t10)} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt ; $($tail:tt)* )       => { __parse_internal!{@BIND($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8 $t9 $t10) $($tail)*} };
    ( @STATEMENT($args:tt $($data:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $($tail:tt)* ) => { __parse_internal!{@STATEMENT($args $($data)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8 $t9 $t10 $t11) $($tail)*} };

    // Public rules:

    // Statement ::= Bind ';'
    //             | Expr ';'
    //           ::= 'let' $pat '=' Expr
    ( let $name:pat = $($tail:tt)+ )                 => { __parse_internal!{@STATEMENT(($name)) $($tail)+} };
    //             | 'let' $ident ':' $ty '=' Expr
    ( let $name:ident : $name_ty:ty = $($tail:tt)+ ) => { __parse_internal!{@STATEMENT(($name:$name_ty)) $($tail)+} };
    //           ::= Expr ';'
    ( $($tail:tt)+ )                                 => { __parse_internal!{@STATEMENT((_)) $($tail)+} };

    ( $e:expr ) => { $e };

    // Empty
    ( )   => { };
}

// FIXME: Update
/*
#[cfg(test)]
mod test {
    /// Override the or-combinator used by parse! to make it possible to use the simplified
    /// test-types.
    macro_rules! __parse_internal_or {
        ($lhs:expr, $rhs:expr) => {
            {
                match ($lhs)(Input(i)) {
                    Data::Value(j, t) => Data::Value(j, t),
                    Data::Error(_, _) => ($rhs)(Input(i)),
                }
            }
        };
    }

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
        fn bind<F, U, V>(self, f: F) -> Data<U, V>
          where F: FnOnce(Input, T) -> Data<U, V>,
                V: From<E> {
            match self {
                // Embedded f(Input(i), t).map_err(From::from),
                // reason is that the API parse! uses is only ret, err, bind and map (in addition
                // to the __parse_internal_or macro).
                Data::Value(i, t) => match f(Input(i), t) {
                    Data::Value(i, t) => Data::Value(i, t),
                    Data::Error(i, e) => Data::Error(i, From::from(e)),
                },
                Data::Error(i, e) => Data::Error(i, From::from(e)),
            }
        }

        fn map<F, U>(self, f: F) -> Data<U, E>
          where F: FnOnce(T) -> U {
            match self {
                Data::Value(i, t) => Data::Value(i, f(t)),
                Data::Error(i, e) => Data::Error(i, e),
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
        let r: Data<_, ()> = parse!{ret "foo"};

        assert_eq!(r, Data::Value(123, "foo"));
    }

    #[test]
    fn ret_typed() {
        let i = Input(123);

        let r = parse!{ret @ _, (): "foo"};

        assert_eq!(r, Data::Value(123, "foo"));
    }

    #[test]
    fn ret_typed2() {
        let i = Input(123);

        let r = parse!{ret @ &str, (): "foo"};

        assert_eq!(r, Data::Value(123, "foo"));
    }

    #[test]
    fn err() {
        let i = Input(123);

        // Type annotation necessary since err leaves T free
        let r: Data<(), _> = parse!{err "foo"};

        assert_eq!(r, Data::Error(123, "foo"));
    }

    #[test]
    fn err_typed() {
        let i = Input(123);

        let r = parse!{err @(), _: "foo"};

        assert_eq!(r, Data::Error(123, "foo"));
    }

    #[test]
    fn err_typed2() {
        let i = Input(123);

        let r = parse!{err @(), &str: "foo"};

        assert_eq!(r, Data::Error(123, "foo"));
    }

    #[test]
    fn action() {
        fn doit(i: Input) -> Data<&'static str, ()> {
            Data::Value(i.0, "doit")
        }

        let i = Input(123);

        let r = parse!(doit());

        assert_eq!(r, Data::Value(123, "doit"));
    }

    #[test]
    fn action2() {
        fn doit(i: Input, p: &str) -> Data<&str, ()> {
            Data::Value(i.0, p)
        }

        let i = Input(123);

        let r = parse!(doit("doit"));

        assert_eq!(r, Data::Value(123, "doit"));
    }

    #[test]
    fn action3() {
        fn doit(i: Input, p: &str, u: u32) -> Data<(&str, u32), ()> {
            Data::Value(i.0, (p, u))
        }

        let i = Input(123);

        let r = parse!(doit("doit", 1337));

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

        let r = parse!(doit(); something());

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

        let r = parse!(doit(22); something(33));

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

        let r = parse!(doit(22, 1); something(33, 2));

        assert_eq!(r, Data::Value(123, (33, 2)));
    }

    #[test]
    fn action_ret() {
        fn doit(i: Input, x: i32) -> Data<i32, ()> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!(i1; doit(2); ret 5);
        let r2              = parse!(i2; doit(2); ret @ _, (): 5);

        assert_eq!(r1, Data::Value(321, 5));
        assert_eq!(r2, Data::Value(321, 5));
    }

    #[test]
    fn action_ret2() {
        fn doit(i: Input, x: i32) -> Data<i32, ()> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }
        fn something(i: Input, n: u32, x: i32) -> Data<(u32, i32), ()> {
            assert_eq!(i.0, 321);

            Data::Value(111, (n, x))
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!{doit(2); something(4, 5); ret 5};
        let r2              = parse!{doit(2); something(4, 5); ret @ _, (): 5};

        assert_eq!(r1, Data::Value(111, 5));
        assert_eq!(r2, Data::Value(111, 5));
    }

    #[test]
    fn bind() {
        fn doit(i: Input, x: i32) -> Data<i32, ()> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!{let n = doit(40); ret n + 2};
        let r2              = parse!{let n = doit(40); ret @ _, (): n + 2};

        assert_eq!(r1, Data::Value(321, 42));
        assert_eq!(r2, Data::Value(321, 42));
    }

    #[test]
    fn bind2() {
        fn doit(i: Input, x: i32) -> Data<i32, ()> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }
        fn something(i: Input, n: i32, x: u32) -> Data<i32, ()> {
            assert_eq!(i.0, 321);

            Data::Value(111, n - x as i32)
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!{let n = doit(40); let x = something(n, 4); ret x + 6};
        let r2              = parse!{let n = doit(40); let x = something(n, 4);
                                  ret @ _, (): x + 6};

        assert_eq!(r1, Data::Value(111, 42));
        assert_eq!(r2, Data::Value(111, 42));
    }

    #[test]
    fn bind3() {
        fn doit(i: Input, x: i32) -> Data<i32, u8> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<(), u8> = parse!{let n = doit(40); err n as u8 + 2};
        let r2               = parse!{let n = doit(40); err @ (), u8: n as u8 + 2};

        assert_eq!(r1, Data::Error(321, 42));
        assert_eq!(r2, Data::Error(321, 42));
    }

    #[test]
    fn bind4() {
        fn doit(i: Input, x: i32) -> Data<i32, u8> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }
        fn something(i: Input, n: i32, x: u32) -> Data<i32, u8> {
            assert_eq!(i.0, 321);

            Data::Value(111, n - x as i32)
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<(), u8> = parse!{let n = doit(40); let x = something(n, 4); err x as u8 + 6};
        let r2               = parse!{let n = doit(40); let x = something(n, 4);
                                  err @ (), u8: x as u8 + 6};

        assert_eq!(r1, Data::Error(111, 42));
        assert_eq!(r2, Data::Error(111, 42));
    }

    #[test]
    fn bind_then() {
        fn doit(i: Input, x: i32) -> Data<i32, ()> {
            assert_eq!(i.0, 111);

            Data::Value(321, x)
        }
        fn something(i: Input, n: i32, x: u32) -> Data<i32, ()> {
            assert_eq!(i.0, 123);

            Data::Value(111, n - x as i32)
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!{let x = something(6, 4); doit(x)};
        let r2              = parse!{let x = something(6, 4); doit(x)};

        assert_eq!(r1, Data::Value(321, 2));
        assert_eq!(r2, Data::Value(321, 2));
    }

    #[test]
    fn bind_then2() {
        fn doit(i: Input, x: i32) -> Data<i32, ()> {
            assert_eq!(i.0, 111);

            Data::Value(321, x)
        }
        fn something(i: Input, n: i32, x: u32) -> Data<i32, ()> {
            assert_eq!(i.0, 123);

            Data::Value(111, n - x as i32)
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!{let _x = something(6, 4); doit(3)};
        let r2              = parse!{let _x = something(6, 4); doit(3)};

        assert_eq!(r1, Data::Value(321, 3));
        assert_eq!(r2, Data::Value(321, 3));
    }

    #[test]
    fn bind_type() {
        fn doit<N>(i: Input, x: N) -> Data<N, ()> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!{let n: u64 = doit(42); ret n};
        let r2              = parse!{let n: u64 = doit(42); ret @ _, (): n};

        assert_eq!(r1, Data::Value(321, 42u64));
        assert_eq!(r2, Data::Value(321, 42u64));
    }

    #[test]
    fn bind_pattern() {
        fn something(i: Input, n: u32, x: u32) -> Data<(u32, u32), ()> {
            assert_eq!(i.0, 123);

            Data::Value(111, (n, x))
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!{let (x, y) = something(2, 4); ret x + y};
        let r2              = parse!{let (x, y) = something(2, 4); ret @ _, (): x + y};

        assert_eq!(r1, Data::Value(111, 6));
        assert_eq!(r2, Data::Value(111, 6));
    }

    #[test]
    fn bind_pattern2() {
        fn doit(i: Input, x: i32) -> Data<i32, ()> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }
        fn something(i: Input, n: i32, x: u32) -> Data<(i32, u32), ()> {
            assert_eq!(i.0, 321);

            Data::Value(111, (n, x))
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!{let n = doit(40); let (x, y) = something(n, 4);
                                  ret x + y as i32};
        let r2              = parse!{let n = doit(40); let (x, y) = something(n, 4);
                                  ret @ _, (): x + y as i32};

        assert_eq!(r1, Data::Value(111, 44));
        assert_eq!(r2, Data::Value(111, 44));
    }

    #[test]
    fn action_err() {
        fn doit(i: Input, x: i32) -> Data<i32, u8> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<(), u8> = parse!(i1; doit(2); err 5);
        let r2               = parse!(i2; doit(2); err @ (), u8: 5);

        assert_eq!(r1, Data::Error(321, 5));
        assert_eq!(r2, Data::Error(321, 5));
    }

    #[test]
    fn action_err2() {
        fn doit(i: Input, x: i32) -> Data<i32, u8> {
            assert_eq!(i.0, 123);

            Data::Value(321, x)
        }
        fn something(i: Input, n: u32, x: i32) -> Data<(u32, i32), u8> {
            assert_eq!(i.0, 321);

            Data::Value(111, (n, x))
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<(), u8> = parse!{doit(2); something(4, 5); err 5};
        let r2               = parse!{doit(2); something(4, 5); err @ (), u8: 5};

        assert_eq!(r1, Data::Error(111, 5));
        assert_eq!(r2, Data::Error(111, 5));
    }

    /*
    #[test]
    fn inline_action() {
        let i = Input(123);

        let r = parse!{i;
            s -> {
                // Essentially just Input(123).ret(23):
                assert_eq!(s, Input(123));

                s.ret::<_, ()>(23)
            }
        };

        assert_eq!(r, Data::Value(123, 23));
    }

    #[test]
    fn inline_action2() {
        fn doit(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Value(321, 2)
        }

        let i = Input(123);

        let r = parse!{i;
            doit();
            s -> {
                // Essentially just Input(123).ret(23):
                assert_eq!(s, Input(321));

                s.ret::<_, ()>(23)
            }
        };

        assert_eq!(r, Data::Value(321, 23));
    }

    #[test]
    fn inline_action3() {
        let i = Input(123);

        let r = parse!{i;
            s -> s.ret::<u8, ()>(23)
        };

        assert_eq!(r, Data::Value(123, 23));
    }

    #[test]
    fn inline_action_bind() {
        let i = Input(123);

        let r = parse!{i;
            let v = s -> {
                assert_eq!(s, Input(123));

                s.ret(23)
            };
            ret @ u32, (): v + 2
        };

        assert_eq!(r, Data::Value(123, 25));
    }

    #[test]
    fn inline_action_bind2() {
        fn doit(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Value(321, 2)
        }

        let i = Input(123);

        let r = parse!{i;
            let n = doit();
            let v = s -> {
                assert_eq!(n, 2);
                assert_eq!(s, Input(321));

                s.ret(23 + n)
            };
            ret @ u32, (): v + 3
        };

        assert_eq!(r, Data::Value(321, 28));
    }
    */

    #[test]
    fn expr_ret() {
        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<_, ()> = parse!{let a = ret "test"; ret a};
        let r2: Data<_, ()> = parse!{ret "throwaway"; ret "foo"};

        assert_eq!(r1, Data::Value(123, "test"));
        assert_eq!(r2, Data::Value(123, "foo"));
    }

    #[test]
    fn expr_err() {
        let i1 = Input(123);
        let i2 = Input(123);

        let r1: Data<&str, &str> = parse!{let a = err "error"; ret a};
        // Necessary with type annotation here since the value type is not defined in the first
        // statement in parse
        let r2: Data<(), &str>   = parse!{err @ (), _: "this"; err "not this"};

        assert_eq!(r1, Data::Error(123, "error"));
        assert_eq!(r2, Data::Error(123, "this"));
    }

    #[test]
    fn alt() {
        fn fail(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Error(456, ())
        }
        fn doit(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Value(321, 2)
        }

        let i1 = Input(123);
        let i2 = Input(123);
        let i3 = Input(123);
        let i4 = Input(123);

        trace_macros!(true);
        let r1 = parse!{fail() <|> doit()};
        trace_macros!(false);
        let r2 = parse!{doit() <|> fail()};
        let r3 = parse!{doit() <|> doit()};
        let r4 = parse!{fail() <|> fail()};

        assert_eq!(r1, Data::Value(321, 2));
        assert_eq!(r2, Data::Value(321, 2));
        assert_eq!(r3, Data::Value(321, 2));
        assert_eq!(r4, Data::Error(456, ()));
    }

    #[test]
    fn alt2() {
        fn fail(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Error(456, ())
        }
        fn doit(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Value(321, 2)
        }

        let i = Input(123);


        let r1 = parse!{fail() <|> fail() <|> doit() };

        assert_eq!(r1, Data::Value(321, 2));
    }

    #[test]
    fn chain_alt() {
        fn fail(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Error(456, ())
        }
        fn doit(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Value(321, 2)
        }
        fn next(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(321));

            Data::Value(322, 42)
        }


        let i1 = Input(123);
        let i2 = Input(123);
        let i3 = Input(123);

        let r1 = parse!{fail() <|> doit(); next() };
        let r2 = parse!{doit() <|> fail(); next() };
        let r3 = parse!{fail() <|> fail(); next() };

        assert_eq!(r1, Data::Value(322, 42));
        assert_eq!(r2, Data::Value(322, 42));
        assert_eq!(r3, Data::Error(456, ()));
    }

    #[test]
    fn precedence_skip_then() {
        fn a(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Value(321, 2)
        }
        fn b(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(321));

            Data::Value(322, 42)
        }
        fn c(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(322));

            Data::Value(323, 43)
        }

        let i1  = Input(123);
        let i2  = Input(123);
        let i3  = Input(123);
        let i4  = Input(123);
        let i5  = Input(123);
        let i6  = Input(123);
        let i7  = Input(123);
        let i_8 = Input(123);
        let i9  = Input(123);
        let i10 = Input(123);
        let i11 = Input(123);
        let i12 = Input(123);

        let r1  = parse!{a() <* b() <* c()};
        let r2  = parse!{a() <* b() >> c()};
        let r3  = parse!{a() >> b() <* c()};
        let r4  = parse!{a() >> b() >> c()};

        let r5  = parse!{ (a() <* b()) <* c()};
        let r6  = parse!{  a() <* (b() <* c())};
        let r7  = parse!{ (a() <* b()) >> c()};
        let r8  = parse!{ a() <* (b() >> c())};
        let r9  = parse!{ (a() >> b()) <* c()};
        let r10 = parse!{ a() >> (b() <* c())};
        let r11 = parse!{(a() >> b()) >> c()};
        let r12 = parse!{ a() >> (b() >> c())};

        assert_eq!(r1, Data::Value(323, 2));
        assert_eq!(r2, Data::Value(323, 43));
        assert_eq!(r3, Data::Value(323, 42));
        assert_eq!(r4, Data::Value(323, 43));

        assert_eq!(r5,  Data::Value(323, 2));
        assert_eq!(r6,  Data::Value(323, 2));
        assert_eq!(r7,  Data::Value(323, 43));
        assert_eq!(r8,  Data::Value(323, 2));
        assert_eq!(r9,  Data::Value(323, 42));
        assert_eq!(r10, Data::Value(323, 42));
        assert_eq!(r11, Data::Value(323, 43));
        assert_eq!(r12, Data::Value(323, 43));
    }

    #[test]
    fn precedence_skip_alt() {
        fn a(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Value(321, 2)
        }
        fn b(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(321));

            Data::Value(322, 42)
        }
        fn c(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(322));

            Data::Value(323, 43)
        }
        // version of c following a:
        fn c_a(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(321));

            Data::Value(323, 43)
        }

        let i1  = Input(123);
        let i2  = Input(123);
        let i3  = Input(123);
        let i4  = Input(123);
        let i5  = Input(123);
        let i6  = Input(123);
        let i7  = Input(123);
        let i_8 = Input(123);
        let i9  = Input(123);
        let i10 = Input(123);
        let i11 = Input(123);
        let i12 = Input(123);

        let r1 = parse!{a() <* b() <* c()};
        let r2 = parse!{a() <* b() <|> c()};
        let r3 = parse!{a() <|> b() <* c()};
        let r4 = parse!{a() <|> b() <|> c()};

        let r5  = parse!{ (a() <*  b()) <* c()};
        let r6  = parse!{ (a() <*  b()) <|> c()};
        let r7  = parse!{ (a() <|> b()) <* c_a()};
        let r8  = parse!{ (a() <|> b()) <|> c()};
        let r9  = parse!{  a() <*  (b() <* c())};
        let r10 = parse!{  a() <*  (b() <|> c())};
        let r11 = parse!{  a() <|> (b() <* c())};
        let r12 = parse!{  a() <|> (b() <|> c())};

        assert_eq!(r1, Data::Value(323, 2));
        assert_eq!(r2, Data::Value(322, 2));
        assert_eq!(r3, Data::Value(321, 2));
        assert_eq!(r4, Data::Value(321, 2));

        assert_eq!(r5, Data::Value(323, 2));
        assert_eq!(r6, Data::Value(322, 2));
        assert_eq!(r7, Data::Value(323, 2));
        assert_eq!(r8, Data::Value(321, 2));
        assert_eq!(r9, Data::Value(323, 2));
        assert_eq!(r10, Data::Value(322, 2));
        assert_eq!(r11, Data::Value(321, 2));
        assert_eq!(r12, Data::Value(321, 2));
    }

    #[test]
    fn precedence_alt_then() {
        fn a(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Value(321, 2)
        }
        fn b(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(321));

            Data::Value(322, 42)
        }
        fn c(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(322));

            Data::Value(323, 43)
        }
        // version of c with check for a's state:
        fn c_a(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(321));

            Data::Value(323, 43)
        }

        let i1  = Input(123);
        let i2  = Input(123);
        let i3  = Input(123);
        let i4  = Input(123);
        let i5  = Input(123);
        let i6  = Input(123);
        let i7  = Input(123);
        let i_8 = Input(123);
        let i9  = Input(123);
        let i10 = Input(123);
        let i11 = Input(123);
        let i12 = Input(123);

        let r1 = parse!{a() <|> b() <|> c()};
        let r2 = parse!{a() <|> b() >> c_a()};
        let r3 = parse!{a() >> b() <|> c()};
        let r4 = parse!{a() >> b() >> c()};

        let r5  = parse!{ (a() <|> b()) <|> c()};
        let r6  = parse!{ (a() <|> b()) >> c_a()};
        let r7  = parse!{ (a() >>  b()) <|> c()};
        let r8  = parse!{ (a() >>  b()) >> c()};
        let r9  = parse!{  a() <|> (b() <|> c())};
        let r10 = parse!{  a() <|> (b() >> c_a())};
        let r11 = parse!{  a() >>  (b() <|> c())};
        let r12 = parse!{  a() >>  (b() >> c())};

        assert_eq!(r1, Data::Value(321, 2));
        assert_eq!(r2, Data::Value(323, 43));
        assert_eq!(r3, Data::Value(322, 42));
        assert_eq!(r4, Data::Value(323, 43));

        assert_eq!(r5, Data::Value(321, 2));
        assert_eq!(r6, Data::Value(323, 43));
        assert_eq!(r7, Data::Value(322, 42));
        assert_eq!(r8, Data::Value(323, 43));
        assert_eq!(r9, Data::Value(321, 2));
        assert_eq!(r10, Data::Value(321, 2));
        assert_eq!(r11, Data::Value(322, 42));
        assert_eq!(r12, Data::Value(323, 43));
    }

    /*
    #[test]
    fn alt_inline_action() {
        let i = Input(123);

        let r: Data<_, ()> = parse!{i;
            (input -> {
                assert_eq!(input, Input(123));

                Data::Value::<u32, ()>(321, 21)
            }) <|> (input -> {
                assert_eq!(input, Input(321));

                Data::Value(333, 42)
            })
        };

        assert_eq!(r, Data::Value(321, 21));
    }

    #[test]
    fn then_inline_action() {
        let i = Input(123);

        let r: Data<_, ()> = parse!{i;
            (input -> {
                assert_eq!(input, Input(123));

                Data::Value(321, 21)
            }) >> (input -> {
                assert_eq!(input, Input(321));

                Data::Value(333, 42)
            })
        };

        assert_eq!(r, Data::Value(333, 42));
    }

    #[test]
    fn skip_inline_action() {
        let i = Input(123);

        let r: Data<_, ()> = parse!{i;
            (input -> {
                assert_eq!(input, Input(123));

                Data::Value(321, 21)
            }) <* (input -> {
                assert_eq!(input, Input(321));

                Data::Value(333, 42)
            })
        };

        assert_eq!(r, Data::Value(333, 21));
    }
    */

    // Test to make sure we do not hit the default macro iteration limit (64)
    #[test]
    fn max_alt() {
        fn a(i: Input) -> Data<u32, ()> {
            assert_eq!(i, Input(123));

            Data::Value(321, 2)
        }

        let i = Input(123);

        let r = parse!{a() <|> a() <|> a() <|> a() <|> a() <|> a() <|> a() <|> a() <|> a()};

        assert_eq!(r, Data::Value(321, 2));
    }
}
*/
