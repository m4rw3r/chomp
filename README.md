# Chomp

[![Build Status](https://travis-ci.org/m4rw3r/chomp.svg?branch=master)](https://travis-ci.org/m4rw3r/chomp)
[![Coverage Status](https://coveralls.io/repos/m4rw3r/chomp/badge.svg?branch=master&service=github)](https://coveralls.io/github/m4rw3r/chomp?branch=master)
[![Crates.io](https://img.shields.io/crates/v/chomp.svg)](https://crates.io/crates/chomp)
[![Documentation](https://img.shields.io/badge/rustdoc-documentation-blue.svg)](http://m4rw3r.github.io/chomp)

Chomp is a fast monadic-style parser combinator library designed to work on stable Rust. It was written as the culmination of the experiments detailed in these blog posts:

* [Part 1](http://m4rw3r.github.io/parser-combinator-experiments-rust/)
* [Part 2](http://m4rw3r.github.io/parser-combinator-experiments-errors)
* [Part 3](http://m4rw3r.github.io/parser-combinator-experiments-part-3)
* [Chomp 0.1 Announcement](http://m4rw3r.github.io/parser-combinators-road-chomp-0-1/)

For its current capabilities, you will find that Chomp performs consistently as well, if not better, than optimized C parsers, while being vastly more expressive. For an example that builds a performant HTTP parser out of smaller parsers, see [http_parser.rs](examples/http_parser.rs).

##Installation

Add the following line to the dependencies section of your `Cargo.toml`:

```toml
[dependencies]
chomp = "0.2.5"
```

##Usage

Parsers are functions from a slice over an input type `Input<I>` to a `ParseResult<I, T, E>`, which may be thought of as either a success resulting in type `T`, an error of type `E`, or a partially completed result which may still consume more input of type `I`.

The input type is almost never manually manipulated. Rather, one uses parsers from Chomp by invoking the `parse!` macro. This macro was designed intentionally to be as close as possible to Haskell's `do`-syntax or F#'s "computation expressions", which are used to sequence monadic computations. At a very high level, usage of this macro allows one to declaratively:

* Sequence parsers, while short circuiting the rest of the parser if any step fails.
* Bind previous successful results to be used later in the computation.
* Return a composite datastructure using the previous results at the end of the computation.

In other words, just as a normal Rust function usually looks something like this:

```rust
fn f() -> (u8, u8, u8) {
    let a = read_digit();
    let b = read_digit();
    launch_missiles();
    return (a, b, a + b);
}
```

A Chomp parser with a similar structure looks like this:

```rust
fn f(i: Input<u8>) -> U8Result<(u8, u8, u8)> {
    parse!{i;
        let a = read_digit();
        let b = read_digit();
        string(b"missiles");
        ret (a, b, a + b);
    }
} 
```

And to implement `read_digit` we can utilize the `map` function to manipulate any success value while preserving any error or incomplete state:

```rust
// Standard rust, no error handling:
fn read_digit() -> u8 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).unwrap();
    s.trim().parse().unwrap()
}

// Chomp, error handling built in, and we make sure we only get a number:
fn read_digit(i: Input<u8>) -> U8Result<u8> {
    satisfy(i, |c| b'0' <= c && c <= b'9').map(|c| c - b'0')
}
```

For more documentation, see the rust-doc output.

## Example

```rust
#[macro_use]
extern crate chomp;

use chomp::{Input, U8Result, parse_only};
use chomp::{take_while1, token};

#[derive(Debug, Eq, PartialEq)]
struct Name<'a> {
    first: &'a [u8],
    last:  &'a [u8],
}

fn name(i: Input<u8>) -> U8Result<Name> {
    parse!{i;
        let first = take_while1(|c| c != b' ');
                    token(b' ');  // skipping this char
        let last  = take_while1(|c| c != b'\n');

        ret Name{
            first: first,
            last:  last,
        }
    }
}

fn main() {
    assert_eq!(parse_only(name, "Martin Wernstål\n".as_bytes()), Ok(Name{
        first: b"Martin",
        last: "Wernstål".as_bytes()
    }));
}
```

##Contact

You can contact the author either through an issue here on GitHub, or you can query him at m4rw3r on mozilla's irc network.
