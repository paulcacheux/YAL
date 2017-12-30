use std::collections::HashMap;

use ir;
use ty;
use string_interner::{StringId, StringInterner};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    Void,
    Int(i64),
    Double(f64),
    Boolean(bool),
    String(StringId),
    LValue(usize),
}

pub fn interpret_program(program: &ir::Program, strings: &StringInterner) {
    let mut interpreter = Interpreter::new(program, strings);

    interpreter.interpret_function_by_name("main", &[]);
    // TODO maybe return int
}

struct Interpreter<'p, 'si> {
    program: &'p ir::Program,
    memory: Memory,
    strings: &'si StringInterner,
}

macro_rules! propagate {
    ($e:expr) => { propagate!($e, {}); };
    ($e:expr, $finally:expr) => {
        match $e {
            s @ StatementResult::Break |
            s @ StatementResult::Continue |
            s @ StatementResult::Return(_) => {
                $finally;
                return s
            }
            _ => {}
        }
    }
}

macro_rules! extract_pattern {
    ($m:expr; $p:pat => $e:expr) => {
        if let $p = $m {
            $e
        } else {
            unreachable!()
        }
    }
}

impl<'p, 'si> Interpreter<'p, 'si> {
    fn new(program: &'p ir::Program, strings: &'si StringInterner) -> Self {
        Interpreter {
            program,
            memory: Memory::new(),
            strings,
        }
    }

    fn interpret_function_by_name(&mut self, name: &str, args: &[Value]) -> Value {
        match name {
            "printInt" => builtins::print_int(self, args),
            "printDouble" => builtins::print_double(self, args),
            "printString" => builtins::print_string(self, args),
            "readInt" => builtins::read_int(self, args),
            "readDouble" => builtins::read_double(self, args),
            name => {
                for function in &self.program.declarations {
                    if function.name == name {
                        return self.interpret_function(function, args);
                    }
                }
                unreachable!()
            }
        }
    }

    fn interpret_function(&mut self, function: &ir::Function, args: &[Value]) -> Value {
        self.memory.begin_scope();
        for (index, &(_, ref param)) in function.parameters.iter().enumerate() {
            self.memory.set_new(param.clone(), args[index]);
        }

        if let StatementResult::Return(ret) = self.interpret_block(&function.body) {
            self.memory.end_scope();
            return ret;
        } else if function.return_ty == ty::Type::Void {
            return Value::Void;
        } else {
            unreachable!()
        }
    }

    fn interpret_block(&mut self, block: &ir::BlockStatement) -> StatementResult {
        self.memory.begin_scope();
        for stmt in block {
            propagate!(self.interpret_statement(stmt), self.memory.end_scope());
        }
        self.memory.end_scope();
        StatementResult::Nothing
    }

    fn interpret_statement(&mut self, stmt: &ir::Statement) -> StatementResult {
        use ir::Statement;
        match *stmt {
            Statement::Block(ref b) => self.interpret_block(b),
            Statement::VarDecl {
                ref name,
                ref value,
                ..
            } => {
                let value = self.interpret_expression(value);
                self.memory.set_new(name.clone(), value);
                StatementResult::Nothing
            }
            Statement::If {
                ref condition,
                ref body,
                ref else_clause,
            } => {
                let condition = self.interpret_expression(condition);
                let condition = extract_pattern!(condition; Value::Boolean(b) => b);
                if condition {
                    propagate!(self.interpret_block(body));
                } else {
                    propagate!(self.interpret_block(else_clause));
                }
                StatementResult::Nothing
            }
            Statement::While {
                ref condition,
                ref body,
            } => {
                loop {
                    let condition = self.interpret_expression(condition);
                    let condition = extract_pattern!(condition; Value::Boolean(b) => b);

                    if !condition {
                        break;
                    }

                    match self.interpret_block(body) {
                        StatementResult::Nothing | StatementResult::Continue => {}
                        StatementResult::Break => break,
                        r @ StatementResult::Return(_) => return r,
                    }
                }
                StatementResult::Nothing
            }
            Statement::Return(ref expr) => {
                let expr = self.interpret_expression(expr);
                StatementResult::Return(expr)
            }
            Statement::Expression(ref expr) => {
                self.interpret_expression(expr);
                StatementResult::Nothing
            }
            Statement::Break => StatementResult::Break,
            Statement::Continue => StatementResult::Continue,
        }
    }

    fn interpret_expression(&mut self, expr: &ir::TypedExpression) -> Value {
        use ir::Expression;

        let ir::TypedExpression { ref ty, ref expr } = *expr;

        match *expr {
            Expression::DefaultValue => {
                match *ty {
                    ty::Type::Int => Value::Int(0),
                    ty::Type::Double => Value::Double(0.0),
                    ty::Type::Boolean => Value::Boolean(false),
                    ty::Type::Void => Value::Void,
                    _ => unreachable!(), // string doesn't have a default value
                }
            }
            Expression::LValueToRValue(ref sub) => {
                let sub = self.interpret_expression(sub);
                let index = extract_pattern!(sub; Value::LValue(v) => v);
                self.memory.value_from_index(index)
            }
            Expression::Literal(lit) => match lit {
                ir::Literal::IntLiteral(i) => Value::Int(i),
                ir::Literal::DoubleLiteral(d) => Value::Double(d),
                ir::Literal::BooleanLiteral(b) => Value::Boolean(b),
                ir::Literal::StringLiteral(s) => Value::String(s),
            },
            Expression::Identifier(ref id) => Value::LValue(self.memory.index_from_name(id)),
            Expression::Assign { ref lhs, ref rhs } => {
                let lhs = self.interpret_expression(lhs);
                let rhs = self.interpret_expression(rhs);
                let index = extract_pattern!(lhs; Value::LValue(v) => v);
                self.memory.set_from_index(index, rhs);
                rhs
            }
            Expression::BinaryOperator {
                binop,
                ref lhs,
                ref rhs,
            } => {
                let lhs = self.interpret_expression(lhs);
                let rhs = self.interpret_expression(rhs);

                use ir::BinaryOperatorKind::*;
                match binop {
                    IntPlus => extract_pattern!(
                        (lhs, rhs);
                        (Value::Int(a), Value::Int(b)) => Value::Int(a + b)
                    ),
                    DoublePlus => extract_pattern!(
                        (lhs, rhs);
                        (Value::Double(a), Value::Double(b)) => Value::Double(a + b)
                    ),
                    IntMinus => extract_pattern!(
                        (lhs, rhs);
                        (Value::Int(a), Value::Int(b)) => Value::Int(a - b)
                    ),
                    DoubleMinus => extract_pattern!(
                        (lhs, rhs);
                        (Value::Double(a), Value::Double(b)) => Value::Double(a - b)
                    ),
                    IntMultiply => extract_pattern!(
                        (lhs, rhs);
                        (Value::Int(a), Value::Int(b)) => Value::Int(a * b)
                    ),
                    DoubleMultiply => extract_pattern!(
                        (lhs, rhs);
                        (Value::Double(a), Value::Double(b)) => Value::Double(a * b)
                    ),
                    IntDivide => extract_pattern!(
                        (lhs, rhs);
                        (Value::Int(a), Value::Int(b)) => Value::Int(a / b)
                    ),
                    DoubleDivide => extract_pattern!(
                        (lhs, rhs);
                        (Value::Double(a), Value::Double(b)) => Value::Double(a / b)
                    ),
                    IntModulo => extract_pattern!(
                        (lhs, rhs);
                        (Value::Int(a), Value::Int(b)) => Value::Int(a % b)
                    ),

                    IntEqual | DoubleEqual | BooleanEqual => Value::Boolean(lhs == rhs),
                    IntNotEqual | DoubleNotEqual | BooleanNotEqual => Value::Boolean(lhs != rhs),
                    IntLess => extract_pattern!(
                        (lhs, rhs);
                        (Value::Int(a), Value::Int(b)) => Value::Boolean(a < b)
                    ),
                    DoubleLess => extract_pattern!(
                        (lhs, rhs);
                        (Value::Double(a), Value::Double(b)) => Value::Boolean(a < b)
                    ),
                    IntLessEqual => extract_pattern!(
                        (lhs, rhs);
                        (Value::Int(a), Value::Int(b)) => Value::Boolean(a <= b)
                    ),
                    DoubleLessEqual => extract_pattern!(
                        (lhs, rhs);
                        (Value::Double(a), Value::Double(b)) => Value::Boolean(a <= b)
                    ),

                    IntGreater => extract_pattern!(
                        (lhs, rhs);
                        (Value::Int(a), Value::Int(b)) => Value::Boolean(a > b)
                    ),
                    DoubleGreater => extract_pattern!(
                        (lhs, rhs);
                        (Value::Double(a), Value::Double(b)) => Value::Boolean(a > b)
                    ),
                    IntGreaterEqual => extract_pattern!(
                        (lhs, rhs);
                        (Value::Int(a), Value::Int(b)) => Value::Boolean(a >= b)
                    ),
                    DoubleGreaterEqual => extract_pattern!(
                        (lhs, rhs);
                        (Value::Double(a), Value::Double(b)) => Value::Boolean(a >= b)
                    ),
                }
            }
            Expression::LazyOperator {
                lazyop,
                ref lhs,
                ref rhs,
            } => {
                let lhs = self.interpret_expression(lhs);

                use ir::LazyOperatorKind::*;
                match lazyop {
                    BooleanLogicalAnd => {
                        if !extract_pattern!(lhs; Value::Boolean(b) => b) {
                            Value::Boolean(false)
                        } else {
                            self.interpret_expression(rhs)
                        }
                    }
                    BooleanLogicalOr => {
                        if extract_pattern!(lhs; Value::Boolean(b) => b) {
                            Value::Boolean(true)
                        } else {
                            self.interpret_expression(rhs)
                        }
                    }
                }
            }
            Expression::UnaryOperator { unop, ref sub } => {
                let sub = self.interpret_expression(sub);

                use ir::UnaryOperatorKind::*;
                match unop {
                    IntMinus => extract_pattern!(sub; Value::Int(i) => Value::Int(-i)),
                    DoubleMinus => extract_pattern!(sub; Value::Double(d) => Value::Double(-d)),
                    BooleanNot => extract_pattern!(sub; Value::Boolean(b) => Value::Boolean(!b)),
                }
            }
            Expression::Increment(ref sub) => {
                let sub = self.interpret_expression(sub);
                let index = extract_pattern!(sub; Value::LValue(i) => i);
                let value = self.memory.value_from_index(index);
                let value = extract_pattern!(value; Value::Int(i) => Value::Int(i + 1));
                self.memory.set_from_index(index, value);
                sub
            }
            Expression::Decrement(ref sub) => {
                let sub = self.interpret_expression(sub);
                let index = extract_pattern!(sub; Value::LValue(i) => i);
                let value = self.memory.value_from_index(index);
                let value = extract_pattern!(value; Value::Int(i) => Value::Int(i - 1));
                self.memory.set_from_index(index, value);
                sub
            }
            Expression::FunctionCall {
                ref function,
                ref args,
            } => {
                let args: Vec<_> = args.into_iter()
                    .map(|arg| self.interpret_expression(arg))
                    .collect();
                self.interpret_function_by_name(function, &args)
            }
        }
    }
}

#[derive(Debug, Clone)]
enum StatementResult {
    Nothing,
    Break,
    Continue,
    Return(Value),
}

struct Memory {
    memory: Vec<Value>, // TODO we don't currently clean the memory
    scopes: Vec<HashMap<String, usize>>,
}

impl Memory {
    fn new() -> Self {
        Memory {
            memory: Vec::new(),
            scopes: Vec::new(),
        }
    }

    fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }

    fn set_new(&mut self, name: String, value: Value) {
        let index = self.memory.len();
        self.memory.push(value);
        self.scopes.last_mut().unwrap().insert(name, index);
    }

    fn set_from_index(&mut self, index: usize, value: Value) {
        self.memory[index] = value;
    }

    fn index_from_name(&self, name: &str) -> usize {
        for scope in self.scopes.iter().rev() {
            if let Some(&value) = scope.get(name) {
                return value;
            }
        }
        unreachable!()
    }

    fn value_from_index(&self, index: usize) -> Value {
        self.memory[index]
    }
}

mod builtins {
    use super::{Interpreter, Value};
    use std::io;

    pub(super) fn print_int(_: &Interpreter, args: &[Value]) -> Value {
        let i = extract_pattern!(args[0]; Value::Int(i) => i);
        println!("{}", i);
        Value::Void
    }

    pub(super) fn print_double(_: &Interpreter, args: &[Value]) -> Value {
        let d = extract_pattern!(args[0]; Value::Double(d) => d);
        println!("{:.1}", d);
        Value::Void
    }

    pub(super) fn print_string(interpreter: &Interpreter, args: &[Value]) -> Value {
        let sid = extract_pattern!(args[0]; Value::String(sid) => sid);
        println!("{}", interpreter.strings.get_str(sid));
        Value::Void
    }

    pub(super) fn read_int(_: &Interpreter, _: &[Value]) -> Value {
        let mut input = String::new();
        io::stdin().read_line(&mut input).expect("STDIN error");
        let trimmed = input.trim();
        Value::Int(trimmed.parse().unwrap())
    }

    pub(super) fn read_double(_: &Interpreter, _: &[Value]) -> Value {
        let mut input = String::new();
        io::stdin().read_line(&mut input).expect("STDIN error");
        let trimmed = input.trim();
        Value::Double(trimmed.parse().unwrap())
    }
}
