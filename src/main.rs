#[macro_use]
extern crate lazy_static;
extern crate regex;
#[macro_use]
extern crate if_chain;

use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

mod lexer;
mod ast;
mod parser;
mod ty;
mod ir;
// mod interpreter;

fn slurp_file<P: AsRef<Path>>(path: P) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut buffer = String::new();
    file.read_to_string(&mut buffer)?;
    Ok(buffer)
}

fn main() {
    let path = std::env::args().nth(1).unwrap();
    let input = slurp_file(path).unwrap();
    let lexer = lexer::Lexer::new(&input);
    let mut parser = parser::Parser::new(lexer);
    let program = parser.parse_program().unwrap();
    let ir = ir::translator::translate_program(program);
    println!("{:#?}", ir);
}
