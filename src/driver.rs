extern crate clap;
extern crate javalette;

use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

use clap::{App, Arg};

use javalette::*;
use span::{Span, Spanned};

fn slurp_file<P: AsRef<Path>>(path: P) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut buffer = String::new();
    file.read_to_string(&mut buffer)?;
    Ok(buffer)
}

fn print_error_line(input: &str, span: Span) {
    let mut arrow = String::with_capacity(input.len());

    for (i, c) in input.chars().enumerate() {
        arrow.push(match c {
            '\n' => '\n',
            '\t' => '\t',
            '\r' => '\r',
            _ if span.start <= i && i < span.end => '^',
            _ => ' ',
        });
    }

    let iter = input
        .lines()
        .map(String::from)
        .zip(arrow.lines().map(String::from))
        .enumerate()
        .filter(|&(_, (_, ref arrow))| arrow.contains('^'));

    for (n, (line, arrow)) in iter {
        eprintln!("{:04}| {}\n    |{}", n, line, arrow);
    }
}

fn continue_or_exit<T, E: std::fmt::Display>(
    path: &str,
    input: &str,
    res: Result<T, Spanned<E>>,
) -> T {
    match res {
        Ok(v) => return v,
        Err(Spanned { inner: error, span }) => {
            eprintln!("{}:{}:{}: {}", path, span.start, span.end, error);
            print_error_line(input, span);
            std::process::exit(1);
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Backend {
    LLVM,
    Interpreter,
}

fn main() {
    let matches = App::new("Javalette interpreter")
        .version("0.1")
        .author("Paul CACHEUX <paulcacheux@gmail.com>")
        .arg(
            Arg::with_name("INPUT")
                .help("Sets the input file.")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("OPT")
                .help("Activate optimizations.")
                .short("O")
                .long("opt"),
        )
        .arg(
            Arg::with_name("BACKEND")
                .help("Choose backend. LLVM by default.")
                .long("backend")
                .takes_value(true)
                .possible_values(&["LLVM", "interpreter"]),
        )
        .get_matches();

    let path = matches.value_of("INPUT").unwrap();
    let opt = matches.is_present("OPT");
    let backend = match matches.value_of("BACKEND") {
        Some("LLVM") => Backend::LLVM,
        Some("interpreter") => Backend::Interpreter,
        _ => Backend::LLVM,
    };

    let input = slurp_file(&path).unwrap();

    let lexer = lexer::Lexer::new(&input);
    let program = continue_or_exit(&path, &input, parser::parse_program(lexer));
    // println!("{:#?}", program);
    let ir_prog = continue_or_exit(&path, &input, ir_translator::translate_program(program));
    // println!("{:#?}", ir_prog);

    match backend {
        Backend::LLVM => {
            let mut llvm_exec = backend::llvm::llvm_gen_program(ir_prog).unwrap();
            // llvm_exec.print_module();
            llvm_exec.verify_module();
            if opt {
                llvm_exec.optimize();
            }
            llvm_exec.call_main();
        }
        Backend::Interpreter => {
            backend::interpreter::interpret_program(&ir_prog).expect("Interpreter error");
        }
    }
}
