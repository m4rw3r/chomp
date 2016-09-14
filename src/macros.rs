/// Macro emulating `do`-notation for the parser monad, automatically threading the linear type.
///
/// ```
/// # #![feature(conservative_impl_trait)]
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::prelude::*;
/// # fn parser<I: Input>(_s: &str) -> impl Parser<I, Output=(), Error=()> { ret(()) }
/// # fn other_parser<I: Input>() -> impl Parser<I, Output=u8, Error=()> { ret(23) }
/// # fn do_something(_i: u8) -> u32 { 23 }
/// # let input = &b"foo"[..];
/// # let _r: (_, Result<_, ()>) =
/// parse!{
///                 parser("parameter");
///     let value = other_parser();
///
///     ret(do_something(value))
/// }
/// # .parse(input);
/// # let _r: (_, Result<_, ()>) =
/// // is equivalent to:
/// parser("parameter").bind(|_|
///     other_parser().bind(|value|
///         ret(do_something(value))))
/// # .parse(input);
/// # }
/// ```
///
/// # Examples
///
/// Parsing into a struct using the basic provided parsers:
///
/// ```
/// # #![feature(conservative_impl_trait)]
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::prelude::{Buffer, Input, Error, Parser, parse_only, take_while1, token, ret};
///
/// #[derive(Debug, Eq, PartialEq)]
/// struct Name<B: Buffer> {
///     first: B,
///     last:  B,
/// }
///
/// fn parser<I: Input<Token=u8>>() -> impl Parser<I, Output=Name<I::Buffer>, Error=Error<u8>> {
///     parse!{
///         let first = take_while1(|c| c != b' ');
///                     token(b' ');
///         let last  = take_while1(|c| c != b'\n');
///
///         ret(Name{
///             first: first,
///             last:  last,
///         })
///     }
/// }
///
/// assert_eq!(parse_only(parser(), "Martin Wernstål\n".as_bytes()), Ok(Name{
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
/// # #![feature(conservative_impl_trait)]
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::prelude::{U8Input, Parser, Error, parse_only, string, token, ret};
/// use chomp::ascii::decimal;
///
/// fn parse_ip<I: U8Input>() -> impl Parser<I, Output=(u8, u8, u8, u8), Error=Error<u8>> {
///     parse!{
///                 string(b"ip:");
///         let a = decimal() <* token(b'.');
///         let b = decimal() <* token(b'.');
///         let c = decimal() <* token(b'.');
///         let d = decimal();
///                 token(b';');
///         ret((a, b, c, d))
///     }
/// }
///
/// assert_eq!(parse_only(parse_ip(), b"ip:192.168.0.1;"), Ok((192, 168, 0, 1)));
/// # }
/// ```
///
/// Parsing a log-level using the `<|>` alternation (or) operator:
///
/// ```
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// use chomp::prelude::{Parser, parse_only, string};
///
/// #[derive(Debug, Eq, PartialEq)]
/// enum Log {
///     Error,
///     Warning,
///     Info,
///     Debug,
/// };
///
/// let level        = |b, r| string(b).map(|_| r);
/// let log_severity = parse!{
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
/// # #![feature(conservative_impl_trait)]
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::ascii::decimal;
/// # use chomp::prelude::{parse_only, U8Input, Error, token, Parser, ret};
/// # fn my_parser<I: U8Input>() -> impl Parser<I, Output=u32, Error=Error<u8>> {
/// parse!{
///     token(b':');
///     let n: u32 = decimal();
///     ret(n * 2)
/// }
/// # }
/// # assert_eq!(parse_only(my_parser(), b":21"), Ok(42));
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
/// # #![feature(conservative_impl_trait)]
/// # #[macro_use] extern crate chomp;
/// # fn main() {
/// # use chomp::prelude::{parse_only, U8Input, Parser, ret};
/// # fn my_parser<I: U8Input>() -> impl Parser<I, Output=&'static str, Error=()> {
/// fn do_it<'a, I: U8Input>(s: &'a str) -> impl Parser<I, Output=&'a str, Error=()> { ret(s) }
///
/// parse!{
///     do_it("second parameter")
/// }
/// # }
/// # assert_eq!(parse_only(my_parser(), b":21"), Ok("second parameter"));
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
/// # use chomp::prelude::{parse_only, ret};
/// let r: Result<_, (_, ())> = parse_only(
///     parse!{ ret("some success data") },
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
/// # use chomp::prelude::{parse_only, err};
/// let r = parse_only(parse!{ err::<u32, _>("some error data") }, b"input data");
///
/// assert_eq!(r, Err((&b"input data"[..], "some error data")));
/// # }
/// ```
///
/// Note that we only declare the success type (`u32` above) and leave out the type of the error
/// (by using `_`) since that can be uniquely inferred.
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
///    # use chomp::ascii::decimal; use chomp::prelude::{Parser, parse_only, token};
///    let p = parse!{ decimal() <* token(b';') };
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
///    # use chomp::prelude::{Parser, parse_only, token};
///    let p = parse!{ token(b'a') <|> token(b'b') };
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
///    # use chomp::prelude::{Parser, parse_only, token};
///    let p = parse!{ token(b'a') >> token(b';') };
///
///    assert_eq!(parse_only(p, b"a;"), Ok(b';'));
///    # }
///    ```
///
/// These operators correspond to the equivalent operators found in Haskell's `Alternative`,
/// `Applicative` and `Monad` typeclasses, with the exception of being right-associative (the
/// operators are left-associative in Haskell).
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
/// # fn main() {}
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
    ( @BIND((_)                         $($exp:tt)+) $($tail:tt)+ ) => { (__parse_internal!{@EXPR() $($exp)* }).bind(move |_| __parse_internal!{$($tail)* }) };
    ( @BIND(($name:pat)                 $($exp:tt)+) $($tail:tt)+ ) => { (__parse_internal!{@EXPR() $($exp)* }).bind(move |$name| __parse_internal!{$($tail)* }) };
    ( @BIND(($name:ident : $name_ty:ty) $($exp:tt)+) $($tail:tt)+ ) => { (__parse_internal!{@EXPR() $($exp)* }).bind(move |$name : $name_ty| __parse_internal!{$($tail)* }) };

    // Term ::= Ret
    //        | Err
    //        | '(' Expr ')'
    //        | Inline
    //        | Named
    // Ret ::= "ret" Typed
    //( @TERM(ret @ $t_ty:ty , $e_ty:ty : $e:expr) )   => { ret::<_, $t_ty, $e_ty>($e) };
    //       | "ret" $expr
    //( @TERM(ret $e:expr) )                           => { ret($e) };
    // Err ::= "err" Typed
    //( @TERM(err @ $t_ty:ty , $e_ty:ty : $e:expr) )   => { err::<_, $t_ty, $e_ty>($e) };
    //       | "err" $expr
    //( @TERM(err $e:expr) )                           => { err($e) };
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
    ( @EXPR($($lhs:tt)*) >> $($tail:tt)* )          => { (__parse_internal!{@EXPR_ALT() $($lhs)*}).bind(move |_| __parse_internal!{@EXPR() $($tail)*}) };
    // recurse until >> or end
    // unrolled:
    // ( @EXPR($($lhs:tt)*) $t1:tt $($tail:tt)* )      => { __parse_internal!{@EXPR($($lhs)* $t1) $($tail)*} };
    ( @EXPR($($lhs:tt)*) $t1:tt )                                                               => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1} };
    ( @EXPR($($lhs:tt)*) $t1:tt >> $($tail:tt)* )                                               => { (__parse_internal!{@EXPR_ALT() $($lhs)* $t1}).bind(move |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt )                                                        => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt >> $($tail:tt)* )                                        => { (__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2}).bind(move |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt )                                                 => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt >> $($tail:tt)* )                                 => { (__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3}).bind(move |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt )                                          => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt >> $($tail:tt)* )                          => { (__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4}).bind(move |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt )                                   => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt >> $($tail:tt)* )                   => { (__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5}).bind(move |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt )                            => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt >> $($tail:tt)* )            => { (__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6}).bind(move |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt )                     => {  __parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7} };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt >> $($tail:tt)* )     => { (__parse_internal!{@EXPR_ALT() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7}).bind(move |_| __parse_internal!{@EXPR() $($tail)*}) };
    ( @EXPR($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $($tail:tt)* ) => {  __parse_internal!{@EXPR($($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) $($tail)*} };

    // ExprAlt ::= ExprSkip
    ( @EXPR_ALT($($lhs:tt)*) )                      => { __parse_internal!{@EXPR_SKIP() $($lhs)*} };
    //           | ExprSkip <|> ExprAlt
    ( @EXPR_ALT($($lhs:tt)*) <|> $($tail:tt)* )     => { __parse_internal!{@EXPR_SKIP() $($lhs)*}.or(__parse_internal!{@EXPR_ALT() $($tail)*}) };
    // recurse until <|> or end
    // unrolled:
    // ( @EXPR_ALT($($lhs:tt)*) $t1:tt $($tail:tt)* )  => { __parse_internal!{@EXPR_ALT($($lhs)* $t1) $($tail)*} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt )                                                               => {  __parse_internal!{@EXPR_SKIP() $($lhs)* $t1} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt <|> $($tail:tt)* )                                              => { (__parse_internal!{@EXPR_SKIP() $($lhs)* $t1}).or(__parse_internal!{@EXPR_ALT() $($tail)*}) };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt )                                                        => {  __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt <|> $($tail:tt)* )                                       => { (__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2}).or(__parse_internal!{@EXPR_ALT() $($tail)*}) };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt )                                                 => {  __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt <|> $($tail:tt)* )                                => { (__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3}).or(__parse_internal!{@EXPR_ALT() $($tail)*}) };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt )                                          => {  __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt <|> $($tail:tt)* )                         => { (__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4}).or(__parse_internal!{@EXPR_ALT() $($tail)*}) };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt )                                   => {  __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt <|> $($tail:tt)* )                  => { (__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5}).or(__parse_internal!{@EXPR_ALT() $($tail)*}) };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt )                            => {  __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt <|> $($tail:tt)* )           => { (__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6}).or(__parse_internal!{@EXPR_ALT() $($tail)*}) };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt )                     => {  __parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7} };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt <|> $($tail:tt)* )    => { (__parse_internal!{@EXPR_SKIP() $($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7}).or(__parse_internal!{@EXPR_ALT() $($tail)*}) };
    ( @EXPR_ALT($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $($tail:tt)* ) => {  __parse_internal!{@EXPR_ALT($($lhs)* $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) $($tail)*} };

    // ExprSkip ::= Term
    ( @EXPR_SKIP($($lhs:tt)*) )                     => { __parse_internal!{@TERM($($lhs)*)} };
    //            | Term <* ExprSkip
    ( @EXPR_SKIP($($lhs:tt)*) <* $($tail:tt)* )     => { __parse_internal!{@TERM($($lhs)*)}.skip(__parse_internal!{@EXPR_SKIP() $($tail)*}) };
    // recurse until <* or end
    // unrolled:
    // ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $($tail:tt)* ) => { __parse_internal!{@EXPR_SKIP($($lhs)* $t1) $($tail)*} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt )                                          => { __parse_internal!{@TERM($($lhs)* $t1)} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt <* $($tail:tt)* )                          => { __parse_internal!{@TERM($($lhs)* $t1)}.skip(__parse_internal!{@EXPR_SKIP() $($tail)*}) };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt )                                   => { __parse_internal!{@TERM($($lhs)* $t1 $t2)} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt <* $($tail:tt)* )                   => { __parse_internal!{@TERM($($lhs)* $t1 $t2)}.skip(__parse_internal!{@EXPR_SKIP() $($tail)*}) };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt $t3:tt )                            => { __parse_internal!{@TERM($($lhs)* $t1 $t2 $t3)} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt $t3:tt <* $($tail:tt)* )            => { __parse_internal!{@TERM($($lhs)* $t1 $t2 $t3)}.skip(__parse_internal!{@EXPR_SKIP() $($tail)*}) };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt )                     => { __parse_internal!{@TERM($($lhs)* $t1 $t2 $t3 $t4)} };
    ( @EXPR_SKIP($($lhs:tt)*) $t1:tt $t2:tt $t3:tt $t4:tt <* $($tail:tt)* )     => { __parse_internal!{@TERM($($lhs)* $t1 $t2 $t3 $t4)}.skip(__parse_internal!{@EXPR_SKIP() $($tail)*}) };
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

    //( $e:expr ) => { $e };

    // Empty
    //( )   => { };
}

// FIXME: Update
#[cfg(test)]
mod test {
    /// Simplified implementation of the Input type, no Copy
    #[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
    struct Input(i64);

    fn ret<T, E>(t: T) -> impl FnOnce(Input) -> (Input, Result<T, E>) {
        move |i| (i, Ok(t))
    }

    fn err<T, E>(e: E) -> impl FnOnce(Input) -> (Input, Result<T, E>) {
        move |i| (i, Err(e))
    }

    trait Parser {
        type Output;
        type Error;

        fn parse(self, Input) -> (Input, Result<Self::Output, Self::Error>);

        fn bind<F, R>(self, f: F) -> BindParser<Self, F, R>
          where F: FnOnce(Self::Output) -> R,
                R: Parser<Error=Self::Error>,
                Self: Sized {
            BindParser { p: self, f: f }
        }

        fn or<P>(self, p: P) -> OrParser<Self, P>
          where P: Parser<Output=Self::Output, Error=Self::Error>,
                Self: Sized {
            OrParser{ p: self, q: p }
        }
        fn skip<P>(self, p: P) -> SkipParser<Self, P>
          where P: Parser<Error=Self::Error>,
                Self: Sized {
            SkipParser{ p: self, q: p }
        }
    }

    struct BindParser<P, F, R>
      where P: Parser,
            F: FnOnce(P::Output) -> R,
            R: Parser<Error=P::Error> {
        p:  P,
        f:  F,
    }

    impl<P, F, R> Parser for BindParser<P, F, R>
      where P: Parser,
            F: FnOnce(P::Output) -> R,
            R: Parser<Error=P::Error> {
        type Output = R::Output;
        type Error  = R::Error;

        #[inline]
        fn parse(self, i: Input) -> (Input, Result<Self::Output, Self::Error>) {
            match self.p.parse(i) {
                (i, Ok(t))  => (self.f)(t).parse(i),
                (i, Err(e)) => (i, Err(e)),
            }
        }
    }

    struct OrParser<P, Q> {
        p: P,
        q: Q,
    }

    impl<P, Q> Parser for OrParser<P, Q>
      where P: Parser,
            Q: Parser<Output=P::Output, Error=P::Error> {
        type Output = P::Output;
        type Error  = P::Error;

        fn parse(self, i: Input) -> (Input, Result<Self::Output, Self::Error>) {
            let m = i.clone();

            match self.p.parse(i) {
                (i, Ok(d))  => (i, Ok(d)),
                (_, Err(_)) => self.q.parse(m),
            }
        }
    }

    struct SkipParser<P, Q> {
        p: P,
        q: Q,
    }

    impl<P, Q> Parser for SkipParser<P, Q>
      where P: Parser,
            Q: Parser<Error=P::Error> {
        type Output = P::Output;
        type Error  = P::Error;

        fn parse(self, i: Input) -> (Input, Result<Self::Output, Self::Error>) {
            // Merge of p.bind(|t| q.map(|_| t))
            match self.p.parse(i) {
                (i, Ok(t))  => match self.q.parse(i) {
                    (i, Ok(_))  => (i, Ok(t)),
                    (i, Err(e)) => (i, Err(e)),
                },
                (i, Err(e)) => (i, Err(e)),
            }
        }
    }

    impl<F, T, E> Parser for F
      where F: FnOnce(Input) -> (Input, Result<T, E>) {
        type Output = T;
        type Error  = E;

        fn parse(self, i: Input) -> (Input, Result<T, E>) {
            self(i)
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
    fn ret_test() {
        let i = Input(123);

        let r: (_, Result<_, ()>) = parse!{ret("foo")}.parse(i);

        assert_eq!(r, (Input(123), Ok("foo")));
    }

    #[test]
    fn ret_test_typed() {
        let i = Input(123);

        let r = parse!{ret::<_, ()>("foo")};

        assert_eq!(r.parse(i), (Input(123), Ok("foo")));
    }

    #[test]
    fn ret_test_typed2() {
        let i = Input(123);

        let r = parse!{ret::<&str, ()>("foo")};

        assert_eq!(r.parse(i), (Input(123), Ok("foo")));
    }

    #[test]
    fn err_test() {
        let i = Input(123);

        // Type annotation necessary since err leaves T free
        let r: (_, Result<(), _>) = parse!{err("foo")}.parse(i);

        assert_eq!(r, (Input(123), Err("foo")));
    }

    #[test]
    fn err_test_typed() {
        let i = Input(123);

        let r = parse!{err::<(), _>("foo")};

        assert_eq!(r.parse(i), (Input(123), Err("foo")));
    }

    #[test]
    fn err_test_typed2() {
        let i = Input(123);

        let r = parse!{err::<(), &str>("foo")};

        assert_eq!(r.parse(i), (Input(123), Err("foo")));
    }

    #[test]
    fn action() {
        fn doit() -> impl Parser<Output=&'static str, Error=()> {
            move |i| (i, Ok("doit"))
        }

        let i = Input(123);

        let r = parse!(doit());

        assert_eq!(r.parse(i), (Input(123), Ok("doit")));
    }

    #[test]
    fn action2() {
        fn doit<'a>(p: &'a str) -> impl Parser<Output=&'a str, Error=()> {
            move |i| (i, Ok(p))
        }

        let i = Input(123);

        let r = parse!(doit("doit"));

        assert_eq!(r.parse(i), (Input(123), Ok("doit")));
    }

    #[test]
    fn action3() {
        fn doit<'a>(p: &'a str, u: u32) -> impl Parser<Output=(&'a str, u32), Error=()> {
            move |i| (i, Ok((p, u)))
        }

        let i = Input(123);

        let r = parse!(doit("doit", 1337));

        assert_eq!(r.parse(i), (Input(123), Ok(("doit", 1337))));
    }

    #[test]
    fn two_actions() {
        fn doit() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(1))
            }
        }
        fn something() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 321);

                (Input(123), Ok(2))
            }
        }

        let i = Input(123);

        let r = parse!(doit(); something());

        assert_eq!(r.parse(i), (Input(123), Ok(2)));
    }

    #[test]
    fn two_actions2() {
        fn doit(n: u32) -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(n))
            }
        }
        fn something(n: u32) -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 321);

                (Input(123), Ok(n))
            }
        }

        let i = Input(123);

        let r = parse!(doit(22); something(33));

        assert_eq!(r.parse(i), (Input(123), Ok(33)));
    }

    #[test]
    fn two_actions3() {
        fn doit(n: u32, x: i32) -> impl Parser<Output=(u32, i32), Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok((n, x)))
            }
        }
        fn something(n: u32, x: i32) -> impl Parser<Output=(u32, i32), Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 321);

                (Input(123), Ok((n, x)))
            }
        }

        let i = Input(123);

        let r = parse!(doit(22, 1); something(33, 2));

        assert_eq!(r.parse(i), (Input(123), Ok((33, 2))));
    }

    #[test]
    fn action_ret() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!(doit(2); ret(5)).parse(i1);
        let r2                     = parse!(doit(2); ret::<_, ()>(5)).parse(i2);

        assert_eq!(r1, (Input(321), Ok(5)));
        assert_eq!(r2, (Input(321), Ok(5)));
    }

    #[test]
    fn action_ret2() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }
        fn something(n: u32, x: i32) -> impl Parser<Output=(u32, i32), Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 321);

                (Input(111), Ok((n, x)))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!{doit(2); something(4, 5); ret(5)}.parse(i1);
        let r2                     = parse!{doit(2); something(4, 5); ret::<_, ()>(5)}.parse(i2);

        assert_eq!(r1, (Input(111), Ok(5)));
        assert_eq!(r2, (Input(111), Ok(5)));
    }

    #[test]
    fn bind() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!{let n = doit(40); ret(n + 2)}.parse(i1);
        let r2                = parse!{let n = doit(40); ret::<_, ()>(n + 2)}.parse(i2);

        assert_eq!(r1, (Input(321), Ok(42)));
        assert_eq!(r2, (Input(321), Ok(42)));
    }

    #[test]
    fn bind2() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }
        fn something(n: i32, x: u32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 321);

                (Input(111), Ok(n - x as i32))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!{let n = doit(40); let x = something(n, 4); ret(x + 6)}.parse(i1);
        let r2                     = parse!{let n = doit(40); let x = something(n, 4); ret::<_, ()>(x + 6)}.parse(i2);

        assert_eq!(r1, (Input(111), Ok(42)));
        assert_eq!(r2, (Input(111), Ok(42)));
    }

    #[test]
    fn bind3() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=u8> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<(), u8>) = parse!{let n = doit(40); err(n as u8 + 2)}.parse(i1);
        let r2                      = parse!{let n = doit(40); err::<(), u8>(n as u8 + 2)}.parse(i2);

        assert_eq!(r1, (Input(321), Err(42)));
        assert_eq!(r2, (Input(321), Err(42)));
    }

    #[test]
    fn bind4() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=u8> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }
        fn something(n: i32, x: u32) -> impl Parser<Output=i32, Error=u8> {
            move |i: Input| {
                assert_eq!(i.0, 321);

                (Input(111), Ok(n - x as i32))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<(), u8>) = parse!{let n = doit(40); let x = something(n, 4); err(x as u8 + 6)}.parse(i1);
        let r2                      = parse!{let n = doit(40); let x = something(n, 4); err::<(), u8>(x as u8 + 6)}.parse(i2);

        assert_eq!(r1, (Input(111), Err(42)));
        assert_eq!(r2, (Input(111), Err(42)));
    }

    #[test]
    fn bind_then() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 111);

                (Input(321), Ok(x))
            }
        }
        fn something(n: i32, x: u32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(111), Ok(n - x as i32))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!{let x = something(6, 4); doit(x)}.parse(i1);
        let r2                     = parse!{let x = something(6, 4); doit(x)}.parse(i2);

        assert_eq!(r1, (Input(321), Ok(2)));
        assert_eq!(r2, (Input(321), Ok(2)));
    }

    #[test]
    fn bind_then2() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 111);

                (Input(321), Ok(x))
            }
        }
        fn something(n: i32, x: u32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(111), Ok(n - x as i32))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!{let _x = something(6, 4); doit(3)}.parse(i1);
        let r2              = parse!{let _x = something(6, 4); doit(3)}.parse(i2);

        assert_eq!(r1, (Input(321), Ok(3)));
        assert_eq!(r2, (Input(321), Ok(3)));
    }

    #[test]
    fn bind_type() {
        fn doit<N>(x: N) -> impl Parser<Output=N, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!{let n: u64 = doit(42); ret(n)}.parse(i1);
        let r2                     = parse!{let n: u64 = doit(42); ret::<_, ()>(n)}.parse(i2);

        assert_eq!(r1, (Input(321), Ok(42u64)));
        assert_eq!(r2, (Input(321), Ok(42u64)));
    }

    #[test]
    fn bind_pattern() {
        fn something(n: u32, x: u32) -> impl Parser<Output=(u32, u32), Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(111), Ok((n, x)))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!{let (x, y) = something(2, 4); ret(x + y)}.parse(i1);
        let r2                     = parse!{let (x, y) = something(2, 4); ret::<_, ()>(x + y)}.parse(i2);

        assert_eq!(r1, (Input(111), Ok(6)));
        assert_eq!(r2, (Input(111), Ok(6)));
    }

    #[test]
    fn bind_pattern2() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }
        fn something(n: i32, x: u32) -> impl Parser<Output=(i32, u32), Error=()> {
            move |i: Input| {
                assert_eq!(i.0, 321);

                (Input(111), Ok((n, x)))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!{let n = doit(40); let (x, y) = something(n, 4); ret(x + y as i32)}.parse(i1);
        let r2                     = parse!{let n = doit(40); let (x, y) = something(n, 4); ret::<_, ()>(x + y as i32)}.parse(i2);

        assert_eq!(r1, (Input(111), Ok(44)));
        assert_eq!(r2, (Input(111), Ok(44)));
    }

    #[test]
    fn action_err() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=u8> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<(), u8>) = parse!(doit(2); err(5)).parse(i1);
        let r2                      = parse!(doit(2); err::<(), u8>(5)).parse(i2);

        assert_eq!(r1, (Input(321), Err(5)));
        assert_eq!(r2, (Input(321), Err(5)));
    }

    #[test]
    fn action_err2() {
        fn doit(x: i32) -> impl Parser<Output=i32, Error=u8> {
            move |i: Input| {
                assert_eq!(i.0, 123);

                (Input(321), Ok(x))
            }
        }
        fn something(n: u32, x: i32) -> impl Parser<Output=(u32, i32), Error=u8> {
            move |i: Input| {
                assert_eq!(i.0, 321);

                (Input(111), Ok((n, x)))
            }
        }

        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<(), u8>) = parse!{doit(2); something(4, 5); err(5)}.parse(i1);
        let r2                      = parse!{doit(2); something(4, 5); err::<(), u8>(5)}.parse(i2);

        assert_eq!(r1, (Input(111), Err(5)));
        assert_eq!(r2, (Input(111), Err(5)));
    }

    // TODO: Replace with inline closures
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

        assert_eq!(r, (Input(123), Ok(23)));
    }

    #[test]
    fn inline_action2() {
        fn doit(i: Input) -> Data<u32, ()> {
            assert_eq!(i.0, Input(123));

            (321, Ok(2))
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

        assert_eq!(r, (321, Ok(23)));
    }

    #[test]
    fn inline_action3() {
        let i = Input(123);

        let r = parse!{i;
            s -> s.ret::<u8, ()>(23)
        };

        assert_eq!(r, (Input(123), Ok(23)));
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

        assert_eq!(r, (Input(123), Ok(25)));
    }

    #[test]
    fn inline_action_bind2() {
        fn doit(i: Input) -> Data<u32, ()> {
            assert_eq!(i.0, Input(123));

            (321, Ok(2))
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

        assert_eq!(r, (321, Ok(28)));
    }
    */

    #[test]
    fn expr_ret() {
        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<_, ()>) = parse!{let a = ret("test"); ret(a)}.parse(i1);
        let r2: (_, Result<_, ()>) = parse!{ret("throwaway"); ret("foo")}.parse(i2);

        assert_eq!(r1, (Input(123), Ok("test")));
        assert_eq!(r2, (Input(123), Ok("foo")));
    }

    #[test]
    fn expr_err() {
        let i1 = Input(123);
        let i2 = Input(123);

        let r1: (_, Result<&str, &str>) = parse!{let a = err("error"); ret(a)}.parse(i1);
        // Necessary with type annotation here since the value type is not defined in the first
        // statement in parse
        let r2: (_, Result<(), &str>)   = parse!{err::<(), _>("this"); err("not this")}.parse(i2);

        assert_eq!(r1, (Input(123), Err("error")));
        assert_eq!(r2, (Input(123), Err("this")));
    }

    #[test]
    fn alt() {
        fn fail() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(456), Err(()))
            }
        }
        fn doit() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(321), Ok(2))
            }
        }

        let r1 = parse!{fail() <|> doit()};
        let r2 = parse!{doit() <|> fail()};
        let r3 = parse!{doit() <|> doit()};
        let r4 = parse!{fail() <|> fail()};

        assert_eq!(r1.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r2.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r3.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r4.parse(Input(123)), (Input(456), Err(())));
    }

    #[test]
    fn alt2() {
        fn fail() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(456), Err(()))
            }
        }
        fn doit() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(321), Ok(2))
            }
        }

        let i = Input(123);

        let r1 = parse!{fail() <|> fail() <|> doit() }.parse(i);

        assert_eq!(r1, (Input(321), Ok(2)));
    }

    #[test]
    fn chain_alt() {
        fn fail() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(456), Err(()))
            }
        }
        fn doit() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(321), Ok(2))
            }
        }
        fn next() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(321));

                (Input(322), Ok(42))
            }
        }

        let r1 = parse!{fail() <|> doit(); next() };
        let r2 = parse!{doit() <|> fail(); next() };
        let r3 = parse!{fail() <|> fail(); next() };

        assert_eq!(r1.parse(Input(123)), (Input(322), Ok(42)));
        assert_eq!(r2.parse(Input(123)), (Input(322), Ok(42)));
        assert_eq!(r3.parse(Input(123)), (Input(456), Err(())));
    }

    #[test]
    fn precedence_skip_then() {
        fn a() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(321), Ok(2))
            }
        }
        fn b() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(321));

                (Input(322), Ok(42))
            }
        }
        fn c() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(322));

                (Input(323), Ok(43))
            }
        }

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

        assert_eq!(r1.parse(Input(123)), (Input(323), Ok(2)));
        assert_eq!(r2.parse(Input(123)), (Input(323), Ok(43)));
        assert_eq!(r3.parse(Input(123)), (Input(323), Ok(42)));
        assert_eq!(r4.parse(Input(123)), (Input(323), Ok(43)));

        assert_eq!(r5.parse(Input(123)),  (Input(323), Ok(2)));
        assert_eq!(r6.parse(Input(123)),  (Input(323), Ok(2)));
        assert_eq!(r7.parse(Input(123)),  (Input(323), Ok(43)));
        assert_eq!(r8.parse(Input(123)),  (Input(323), Ok(2)));
        assert_eq!(r9.parse(Input(123)),  (Input(323), Ok(42)));
        assert_eq!(r10.parse(Input(123)), (Input(323), Ok(42)));
        assert_eq!(r11.parse(Input(123)), (Input(323), Ok(43)));
        assert_eq!(r12.parse(Input(123)), (Input(323), Ok(43)));
    }

    #[test]
    fn precedence_skip_alt() {
        fn a() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(321), Ok(2))
            }
        }
        fn b() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(321));

                (Input(322), Ok(42))
            }
        }
        fn c() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(322));

                (Input(323), Ok(43))
            }
        }
        // version of c following a:
        fn c_a() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(321));

                (Input(323), Ok(43))
            }
        }

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

        assert_eq!(r1.parse(Input(123)), (Input(323), Ok(2)));
        assert_eq!(r2.parse(Input(123)), (Input(322), Ok(2)));
        assert_eq!(r3.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r4.parse(Input(123)), (Input(321), Ok(2)));

        assert_eq!(r5.parse(Input(123)), (Input(323), Ok(2)));
        assert_eq!(r6.parse(Input(123)), (Input(322), Ok(2)));
        assert_eq!(r7.parse(Input(123)), (Input(323), Ok(2)));
        assert_eq!(r8.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r9.parse(Input(123)), (Input(323), Ok(2)));
        assert_eq!(r10.parse(Input(123)), (Input(322), Ok(2)));
        assert_eq!(r11.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r12.parse(Input(123)), (Input(321), Ok(2)));
    }

    #[test]
    fn precedence_alt_then() {
        fn a() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(321), Ok(2))
            }
        }
        fn b() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(321));

                (Input(322), Ok(42))
            }
        }
        fn c() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(322));

                (Input(323), Ok(43))
            }
        }
        // version of c with check for a's state:
        fn c_a() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(321));

                (Input(323), Ok(43))
            }
        }

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

        assert_eq!(r1.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r2.parse(Input(123)), (Input(323), Ok(43)));
        assert_eq!(r3.parse(Input(123)), (Input(322), Ok(42)));
        assert_eq!(r4.parse(Input(123)), (Input(323), Ok(43)));

        assert_eq!(r5.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r6.parse(Input(123)), (Input(323), Ok(43)));
        assert_eq!(r7.parse(Input(123)), (Input(322), Ok(42)));
        assert_eq!(r8.parse(Input(123)), (Input(323), Ok(43)));
        assert_eq!(r9.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r10.parse(Input(123)), (Input(321), Ok(2)));
        assert_eq!(r11.parse(Input(123)), (Input(322), Ok(42)));
        assert_eq!(r12.parse(Input(123)), (Input(323), Ok(43)));
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

                (Input(333), Ok(42))
            })
        };

        assert_eq!(r, (Input(321), Ok(21)));
    }

    #[test]
    fn then_inline_action() {
        let i = Input(123);

        let r: Data<_, ()> = parse!{i;
            (input -> {
                assert_eq!(input, Input(123));

                (Input(321), Ok(21))
            }) >> (input -> {
                assert_eq!(input, Input(321));

                (Input(333), Ok(42))
            })
        };

        assert_eq!(r, (Input(333), Ok(42)));
    }

    #[test]
    fn skip_inline_action() {
        let i = Input(123);

        let r: Data<_, ()> = parse!{i;
            (input -> {
                assert_eq!(input, Input(123));

                (Input(321), Ok(21))
            }) <* (input -> {
                assert_eq!(input, Input(321));

                (Input(333), Ok(42))
            })
        };

        assert_eq!(r, (Input(333), Ok(21)));
    }
    */

    // Test to make sure we do not hit the default macro iteration limit (64)
    #[test]
    fn max_alt() {
        fn a() -> impl Parser<Output=u32, Error=()> {
            move |i: Input| {
                assert_eq!(i, Input(123));

                (Input(321), Ok(2))
            }
        }

        let i = Input(123);

        let r = parse!{a() <|> a() <|> a() <|> a() <|> a() <|> a() <|> a() <|> a() <|> a()};

        assert_eq!(r.parse(i), (Input(321), Ok(2)));
    }
}
