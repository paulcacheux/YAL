#[macro_use]
extern crate if_chain;
#[macro_use]
extern crate lazy_static;
extern crate regex;

use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

mod string_interner;
mod lexer;
mod ast;
mod parser;
mod ty;
mod ir;
mod interpreter;

fn slurp_file<P: AsRef<Path>>(path: P) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut buffer = String::new();
    file.read_to_string(&mut buffer)?;
    Ok(buffer)
}

fn main() {
    let path = std::env::args().nth(1).unwrap();
    let input = slurp_file(path).unwrap();

    let mut string_interner = string_interner::StringInterner::new();

    let lexer = lexer::Lexer::new(&input);
    let program = {
        let mut parser = parser::Parser::new(lexer, &mut string_interner);
        parser.parse_program().unwrap()
    };
    // println!("{:#?}", program);
    let ir_prog = ir::translator::translate_program(program).unwrap();
    // println!("{:#?}", ir_prog);
    interpreter::interpret_program(&ir_prog, &string_interner);
}
