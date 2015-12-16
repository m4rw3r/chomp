// error-pattern:error: unexpected token: `@`

#[macro_use]
extern crate chomp;

use chomp::{Input, ParseResult, parse_only};

fn parser(i: Input<u8>) -> ParseResult<u8, u8, ()> {
    fn f(i: Input<u8>) -> ParseResult<u8, u8, ()> {
        i.ret(3)
    }

    parse!{i;
        let x = f()
    }
}

fn main() {
    let r = parse_only(parser, b"5");
}
