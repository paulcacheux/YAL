#[macro_use]
extern crate if_chain;
#[macro_use]
extern crate lazy_static;
extern crate libc;
extern crate llvm_sys as llvm;
extern crate regex;
extern crate typed_arena;

pub mod context;
pub mod errors;
pub mod interner;
pub mod codemap;
pub mod lexer;
pub mod ast;
pub mod parser;
pub mod common;
pub mod ty;
pub mod ir;
pub mod trans;
pub mod backend;
