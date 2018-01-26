extern crate clap;
extern crate javalette;

use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

use clap::{App, Arg};

use javalette::*;
use codemap::{CodeMap, Span, Spanned};

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

    if span.end >= input.len() {
        unsafe {
            let bytes = arrow.as_bytes_mut();
            *bytes.last_mut().unwrap() = b'^';
        }
    }

    let iter = input
        .lines()
        .map(String::from)
        .zip(arrow.lines().map(String::from))
        .enumerate()
        .filter(|&(_, (_, ref arrow))| arrow.contains('^'));

    for (n, (line, arrow)) in iter {
        eprintln!("{:05}|{}", n + 1, line);
        eprintln!("     |{}", arrow);
    }
}

fn continue_or_exit<T, E: std::fmt::Display>(
    path: &str,
    codemap: &CodeMap,
    res: Result<T, Spanned<E>>,
) -> T {
    match res {
        Ok(v) => v,
        Err(Spanned { inner: error, span }) => {
            println!("{:?}", span);
            let source_loc = codemap.bytepos_to_sourceloc(span.start);
            eprintln!(
                "{}:{}:{}: {}",
                path, source_loc.line, source_loc.column, error
            );
            eprintln!("{}", error);
            print_error_line(codemap.input, span);
            std::process::exit(1);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BackendType {
    Check,
    JIT,
    Interpreter,
}

#[derive(Debug, Clone)]
struct Options<'a> {
    input_path: &'a str,
    backend: BackendType,
    opt: bool,
    print_ir: bool,
    print_ast: bool,
    print_llvm: bool,
}

impl<'a> Options<'a> {
    fn from_matches(matches: &'a clap::ArgMatches) -> Self {
        let input_path = matches.value_of("INPUT").unwrap();
        let opt = matches.is_present("OPT");
        let mut print_ast = false;
        let mut print_ir = false;
        let mut print_llvm = false;
        if let Some(values) = matches.values_of("DEBUG") {
            for value in values {
                match value {
                    "ir" => print_ir = true,
                    "ast" => print_ast = true,
                    "llvm" => print_llvm = true,
                    _ => {}
                }
            }
        }

        let backend = match matches.value_of("BACKEND") {
            Some("jit") => BackendType::JIT,
            Some("interpreter") => BackendType::Interpreter,
            _ => BackendType::Check,
        };

        Options {
            input_path,
            backend,
            opt,
            print_ir,
            print_ast,
            print_llvm,
        }
    }
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
                .help("Choose backend. Only check by default.")
                .long("backend")
                .takes_value(true)
                .possible_values(&["jit", "interpreter", "check"]),
        )
        .arg(
            Arg::with_name("DEBUG")
                .help("Print debug information to stderr.")
                .long("debug")
                .takes_value(true)
                .multiple(true)
                .possible_values(&["ir", "ast", "llvm"]),
        )
        .get_matches();

    let options = Options::from_matches(&matches);

    let input = slurp_file(options.input_path).unwrap();
    let codemap = codemap::CodeMap::new(options.input_path, &input);

    let mut string_interner = interner::Interner::<String>::new();
    let lexer = lexer::Lexer::new(&input);
    let ast = continue_or_exit(
        options.input_path,
        &codemap,
        parser::parse_program(lexer, &mut string_interner),
    );
    if options.print_ast {
        eprintln!("{:#?}", ast);
    }

    let ir_prog = continue_or_exit(
        options.input_path,
        &codemap,
        ir_translator::translate_program(ast),
    );
    if options.print_ir {
        let mut w = std::io::stderr();
        let mut pp = ir::prettyprinter::PrettyPrinter::new(&mut w);
        pp.pp_program(&ir_prog).expect("ir_pp error");
    }

    if options.backend == BackendType::Check {
        return;
    }

    let mut llvm_exec = backend::llvm_gen_program(ir_prog, &string_interner);
    llvm_exec.verify_module();
    if options.opt {
        llvm_exec.optimize();
    }
    if options.print_llvm {
        llvm_exec.print_module();
    }

    match options.backend {
        BackendType::Check => {}
        BackendType::JIT => llvm_exec.jit_main().expect("run jit error"),
        BackendType::Interpreter => llvm_exec.interpret_main().expect("run interpreter error"),
    }
}
