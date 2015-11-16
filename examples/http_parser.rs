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
use std::fs::File;
use std::env;

#[macro_use]
extern crate chomp;

use chomp::*;

#[derive(Debug)]
struct Request<'a> {
    method:  &'a [u8],
    uri:     &'a [u8],
    version: &'a [u8],
}

#[derive(Debug)]
struct Header<'a> {
    name:  &'a [u8],
    value: Vec<&'a [u8]>,
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

fn end_of_line(i: Input<u8>) -> U8Result<u8> {
    or(i, |i| parse!{i;
               token(b'\r');
               token(b'\n');
               ret b'\r'},
          |i| token(i, b'\n'))
}

fn http_version(i: Input<u8>) -> U8Result<&[u8]> {
    parse!{i;
        string(b"HTTP/");
        take_while1(is_http_version)
    }
}

fn request_line(i: Input<u8>) -> U8Result<Request> {
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

fn message_header_line(i: Input<u8>) -> U8Result<&[u8]> {
    parse!{i;
                   take_while1(is_horizontal_space);
        let line = take_till(is_end_of_line);
                   end_of_line();

        ret line
    }
}

fn message_header(i: Input<u8>) -> U8Result<Header> {
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

fn request(i: Input<u8>) -> U8Result<(Request, Vec<Header>)> {
    parse!{i;
        let r = request_line();
                end_of_line();
        let h = many(message_header);
                end_of_line();

        ret (r, h)
    }
}

fn main() {
    // TODO: Replace with mmap:ed file instead of reading everything into RAM at once.
    let mut contents: Vec<u8> = Vec::new();

    {
        use std::io::Read;

        let mut file = File::open(env::args().nth(1).expect("File to read")).ok().expect("Failed to open file");

        let _ = file.read_to_end(&mut contents).unwrap();
    }

    let i = Iter::new(&contents, request);

    println!("num: {}", i.count());
}
