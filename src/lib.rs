#[macro_use]
extern crate if_chain;
#[macro_use]
extern crate lazy_static;
extern crate regex;
extern crate llvm_sys as llvm;
extern crate libc;

pub mod errors;
pub mod string_interner;
pub mod span;
pub mod lexer;
pub mod ast;
pub mod parser;
pub mod ty;
pub mod ir;
pub mod interpreter;
pub mod llvm_backend;
