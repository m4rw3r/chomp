# Chomp

Chomp is a fast parser combinator designed to work on stable Rust.

## Example

```rust
#[macro_use]
extern crate chomp;

use chomp::{Input, ParseResult, Error};
use chomp::{take_while1, token};

#[derive(Debug, Eq, PartialEq)]
struct Name<'a> {
    first: &'a [u8],
    last:  &'a [u8],
}

fn main() {
    let i = Input::new("martin wernstål\n".as_bytes());

    let r = parse!{i;
        let first = take_while1(|c| c != b' ');
                    token(b' ');
        let last  = take_while1(|c| c != b'\n');

        ret @ _, Error<_>: Name{
            first: first,
            last:  last,
        }
    };

     assert_eq!(r.unwrap(), Name{first: b"martin", last: "wernstål".as_bytes()});
}
```

## [Documentation](http://m4rw3r.github.io/chomp/chomp/index.html)
