#[macro_use]
extern crate if_chain;
#[macro_use]
extern crate lazy_static;
extern crate libc;
extern crate llvm_sys as llvm;
extern crate regex;

pub mod errors;
pub mod interner;
pub mod codemap;
pub mod lexer;
pub mod ast;
pub mod parser;
pub mod ty;
pub mod ir;
pub mod ir_pp;
pub mod ir_translator;
pub mod backend;
