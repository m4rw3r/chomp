//! http parser comparable to the http-parser found in attoparsec's examples.
//!
//! Reads data in the following format:
//!
//! ```text
//! GET /robot.txt HTTP/1.1
//! Host: localhost
//! Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8
//!
//! ```

#[macro_use]
extern crate chomp;

use std::fs::File;
use std::env;

use chomp::prelude::*;

use chomp::buffer::{Source, Stream, StreamError};

#[derive(Debug)]
struct Request<B> {
    method:  B,
    uri:     B,
    version: B,
}

#[derive(Debug)]
struct Header<B> {
    name:  B,
    value: Vec<B>,
}

fn is_token(c: u8) -> bool {
    match c {
        128...255 => false,
        0...31    => false,
        b'('      => false,
        b')'      => false,
        b'<'      => false,
        b'>'      => false,
        b'@'      => false,
        b','      => false,
        b';'      => false,
        b':'      => false,
        b'\\'     => false,
        b'"'      => false,
        b'/'      => false,
        b'['      => false,
        b']'      => false,
        b'?'      => false,
        b'='      => false,
        b'{'      => false,
        b'}'      => false,
        b' '      => false,
        _         => true,
    }
}

fn is_horizontal_space(c: u8) -> bool { c == b' ' || c == b'\t' }
fn is_space(c: u8)            -> bool { c == b' ' }
fn is_not_space(c: u8)        -> bool { c != b' ' }
fn is_end_of_line(c: u8)      -> bool { c == b'\r' || c == b'\n' }
fn is_http_version(c: u8)     -> bool { c >= b'0' && c <= b'9' || c == b'.' }

fn end_of_line<I: Input<Token=u8>>(i: I) -> SimpleResult<I, u8> {
    or(i, |i| parse!{i;
               token(b'\r');
               token(b'\n');
               ret b'\r'},
          |i| token(i, b'\n'))
}

fn http_version<I: Input<Token=u8>>(i: I) -> SimpleResult<I, I::Buffer> {
    parse!{i;
        string(b"HTTP/");
        take_while1(is_http_version)
    }
}

fn request_line<I: Input<Token=u8>>(i: I) -> SimpleResult<I, Request<I::Buffer>> {
    parse!{i;
        let method  = take_while1(is_token);
                      take_while1(is_space);
        let uri     = take_while1(is_not_space);
                      take_while1(is_space);
        let version = http_version();

        ret Request {
            method:  method,
            uri:     uri,
            version: version,
        }
    }
}

fn message_header_line<I: Input<Token=u8>>(i: I) -> SimpleResult<I, I::Buffer> {
    parse!{i;
                   take_while1(is_horizontal_space);
        let line = take_till(is_end_of_line);
                   end_of_line();

        ret line
    }
}

fn message_header<I: Input<Token=u8>>(i: I) -> SimpleResult<I, Header<I::Buffer>> {
    parse!{i;
        let name  = take_while1(is_token);
                    token(b':');
        let lines = many1(message_header_line);

        ret Header {
            name:  name,
            value: lines,
        }
    }
}

fn request<I: Input<Token=u8>>(i: I) -> SimpleResult<I, (Request<I::Buffer>, Vec<Header<I::Buffer>>)> {
    parse!{i;
        let r = request_line();
                end_of_line();
        let h = many(message_header);
                end_of_line();

        ret (r, h)
    }
}

fn main() {
    let file  = File::open(env::args().nth(1).expect("File to read")).ok().expect("Failed to open file");
    // Use default buffer settings for a Read source
    let mut i = Source::new(file);
    let mut n = 0;

    loop {
        match i.parse(request) {
            Ok(_)                        => n += 1,
            Err(StreamError::Retry)      => {}, // Needed to refill buffer when necessary
            Err(StreamError::EndOfInput) => break,
            Err(e)                       => { panic!("{:?}", e); }
        }
    }

    println!("num: {}", n);
}
