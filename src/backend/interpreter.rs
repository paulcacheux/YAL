use std::collections::HashMap;

use ir;
use ty;
use interner::InternerId;
use codemap::Span;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    Null,
    Void,
    Int(i64),
    Double(f64),
    Boolean(bool),
    String(InternerId),
    LValue(usize),
    Array(ArrayId),
}

#[derive(Debug, Clone, Copy)]
pub enum InterpreterError {
    PathWithoutReturn(Span),
}

pub type InterpreterResult<T> = Result<T, InterpreterError>;

pub fn interpret_program(program: &ir::Program) -> InterpreterResult<()> {
    let mut interpreter = Interpreter::new(program);

    // TODO maybe return int
    interpreter
        .interpret_function_by_name("main", &[])
        .map(|_| ())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArrayId(usize);

struct Interpreter<'p> {
    program: &'p ir::Program,
    memory: Memory,
    arrays: Vec<Vec<Value>>,
}

macro_rules! propagate {
    ($e:expr) => { propagate!($e, {}); };
    ($e:expr, $finally:expr) => {
        match $e {
            s @ StatementResult::Break |
            s @ StatementResult::Continue |
            s @ StatementResult::Return(_) => {
                $finally;
                return Ok(s)
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

impl<'p> Interpreter<'p> {
    fn new(program: &'p ir::Program) -> Self {
        Interpreter {
            program,
            memory: Memory::new(),
            arrays: Vec::new(),
        }
    }

    fn new_array(&mut self, values: Vec<Value>) -> ArrayId {
        let index = self.arrays.len();
        self.arrays.push(values);
        ArrayId(index)
    }

    fn interpret_function_by_name(
        &mut self,
        name: &str,
        args: &[Value],
    ) -> InterpreterResult<Value> {
        match name {
            "printInt" => Ok(builtins::print_int(self, args)),
            "printDouble" => Ok(builtins::print_double(self, args)),
            "printString" => Ok(builtins::print_string(self, args)),
            "readInt" => Ok(builtins::read_int(self, args)),
            "readDouble" => Ok(builtins::read_double(self, args)),
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

    fn interpret_function(
        &mut self,
        function: &ir::Function,
        args: &[Value],
    ) -> InterpreterResult<Value> {
        self.memory.begin_scope();
        for (index, &(_, param_id)) in function.parameters.iter().enumerate() {
            self.memory.set_new(param_id, args[index]);
        }

        if let StatementResult::Return(ret) = self.interpret_block(&function.body)? {
            self.memory.end_scope();
            Ok(ret)
        } else if function.return_ty == ty::Type::Void {
            Ok(Value::Void)
        } else {
            Err(InterpreterError::PathWithoutReturn(function.span))
        }
    }

    fn interpret_block(&mut self, block: &[ir::Statement]) -> InterpreterResult<StatementResult> {
        self.memory.begin_scope();
        for stmt in block {
            propagate!(self.interpret_statement(stmt)?, self.memory.end_scope());
        }
        self.memory.end_scope();
        Ok(StatementResult::Nothing)
    }

    fn interpret_statement(&mut self, stmt: &ir::Statement) -> InterpreterResult<StatementResult> {
        use ir::Statement;
        match *stmt {
            Statement::Block(ref b) => self.interpret_block(b),
            Statement::VarDecl {
                ref ty,
                id,
                ref init,
            } => {
                let value = if let Some(ref init) = *init {
                    self.interpret_expression(init)?
                } else {
                    default_value(ty)
                };
                self.memory.set_new(id, value);
                Ok(StatementResult::Nothing)
            }
            Statement::If {
                ref condition,
                ref body,
                ref else_clause,
            } => {
                let condition = self.interpret_expression(condition)?;
                let condition = extract_pattern!(condition; Value::Boolean(b) => b);
                if condition {
                    propagate!(self.interpret_block(body)?);
                } else {
                    propagate!(self.interpret_block(else_clause)?);
                }
                Ok(StatementResult::Nothing)
            }
            Statement::While {
                ref condition,
                ref body,
            } => {
                loop {
                    let condition = self.interpret_expression(condition)?;
                    let condition = extract_pattern!(condition; Value::Boolean(b) => b);

                    if !condition {
                        break;
                    }

                    match self.interpret_block(body)? {
                        StatementResult::Nothing | StatementResult::Continue => {}
                        StatementResult::Break => break,
                        r @ StatementResult::Return(_) => return Ok(r),
                    }
                }
                Ok(StatementResult::Nothing)
            }
            Statement::Return(ref expr) => {
                if let Some(ref expr) = *expr {
                    let expr = self.interpret_expression(expr)?;
                    Ok(StatementResult::Return(expr))
                } else {
                    Ok(StatementResult::Return(Value::Void))
                }
            }
            Statement::Expression(ref expr) => {
                self.interpret_expression(expr)?;
                Ok(StatementResult::Nothing)
            }
            Statement::Break => Ok(StatementResult::Break),
            Statement::Continue => Ok(StatementResult::Continue),
        }
    }

    fn interpret_expression(&mut self, expr: &ir::TypedExpression) -> InterpreterResult<Value> {
        use ir::Expression;

        let ir::TypedExpression { ref expr, .. } = *expr;

        match *expr {
            Expression::Block(ref block) => {
                for stmt in &block.stmts {
                    self.interpret_statement(stmt)?;
                }
                self.interpret_expression(&block.final_expr)
            }
            Expression::LValueToRValue(ref sub) => {
                let sub = self.interpret_expression(sub)?;
                Ok(self.memory.value_from_lvalue(sub))
            }
            Expression::Literal(lit) => Ok(match lit {
                ir::Literal::IntLiteral(i) => Value::Int(i),
                ir::Literal::DoubleLiteral(d) => Value::Double(d),
                ir::Literal::BooleanLiteral(b) => Value::Boolean(b),
                ir::Literal::StringLiteral(s) => Value::String(s),
            }),
            Expression::Identifier(id) => Ok(self.memory.index_from_identifier(id)),
            Expression::Assign { ref lhs, ref rhs } => {
                let lhs = self.interpret_expression(lhs)?;
                let rhs = self.interpret_expression(rhs)?;
                self.memory.set_from_lvalue(lhs, rhs);
                Ok(rhs)
            }
            Expression::BinaryOperator {
                binop,
                ref lhs,
                ref rhs,
            } => {
                let lhs = self.interpret_expression(lhs)?;
                let rhs = self.interpret_expression(rhs)?;

                use ir::BinaryOperatorKind::*;
                Ok(match binop {
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
                })
            }
            Expression::UnaryOperator { unop, ref sub } => {
                let sub = self.interpret_expression(sub)?;

                use ir::UnaryOperatorKind::*;
                Ok(match unop {
                    IntMinus => extract_pattern!(sub; Value::Int(i) => Value::Int(-i)),
                    DoubleMinus => extract_pattern!(sub; Value::Double(d) => Value::Double(-d)),
                    BooleanNot => extract_pattern!(sub; Value::Boolean(b) => Value::Boolean(!b)),
                })
            }
            Expression::Increment(ref sub) => {
                let sub = self.interpret_expression(sub)?;
                let value = self.memory.value_from_lvalue(sub);
                let value = extract_pattern!(value; Value::Int(i) => Value::Int(i + 1));
                self.memory.set_from_lvalue(sub, value);
                Ok(sub)
            }
            Expression::Decrement(ref sub) => {
                let sub = self.interpret_expression(sub)?;
                let value = self.memory.value_from_lvalue(sub);
                let value = extract_pattern!(value; Value::Int(i) => Value::Int(i - 1));
                self.memory.set_from_lvalue(sub, value);
                Ok(sub)
            }
            Expression::Subscript {
                ref array,
                ref index,
            } => {
                let array = self.interpret_expression(array)?;
                let index = self.interpret_expression(index)?;

                let array_index = extract_pattern!(array; Value::Array(ArrayId(id)) => id);
                let real_index = extract_pattern!(index; Value::Int(i) => i as usize);
                Ok(self.arrays[array_index][real_index])
            }
            Expression::FunctionCall {
                ref function,
                ref args,
            } => {
                let args: Result<Vec<_>, _> = args.into_iter()
                    .map(|arg| self.interpret_expression(arg))
                    .collect();
                self.interpret_function_by_name(function, &(args?))
            }
            Expression::NewArray { .. } => unimplemented!(),
            Expression::ArrayLength(ref array) => {
                let array = self.interpret_expression(array)?;
                let array_index = extract_pattern!(array; Value::Array(ArrayId(id)) => id);
                Ok(Value::Int(self.arrays[array_index].len() as _))
            }
        }
    }

    fn create_array(&mut self, base_ty: &ty::Type, sizes: &[usize]) -> Value {
        if !sizes.is_empty() {
            let size = *sizes.first().unwrap();
            let mut values = Vec::with_capacity(size);
            for _ in 0..size {
                let expr = self.create_array(base_ty, &sizes[1..]);
                values.push(self.memory.set_new_unnamed(expr));
            }
            let id = self.new_array(values);
            Value::Array(id)
        } else {
            default_value(base_ty)
        }
    }
}

fn default_value(ty: &ty::Type) -> Value {
    match *ty {
        ty::Type::Int => Value::Int(0),
        ty::Type::Double => Value::Double(0.0),
        ty::Type::Boolean => Value::Boolean(false),
        ty::Type::Void => Value::Void,
        _ => Value::Null,
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
    scopes: Vec<HashMap<ir::IdentifierId, Value>>,
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

    fn set_new_unnamed(&mut self, value: Value) -> Value {
        let index = self.memory.len();
        self.memory.push(value);
        Value::LValue(index)
    }

    fn set_new(&mut self, id: ir::IdentifierId, value: Value) {
        let lvalue = self.set_new_unnamed(value);
        self.scopes.last_mut().unwrap().insert(id, lvalue);
    }

    fn set_from_lvalue(&mut self, lvalue: Value, value: Value) {
        let index = extract_pattern!(lvalue; Value::LValue(index) => index);
        self.memory[index] = value;
    }

    fn index_from_identifier(&self, id: ir::IdentifierId) -> Value {
        for scope in self.scopes.iter().rev() {
            if let Some(&value) = scope.get(&id) {
                return value;
            }
        }
        unreachable!()
    }

    fn value_from_lvalue(&self, lvalue: Value) -> Value {
        let index = extract_pattern!(lvalue; Value::LValue(index) => index);
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
        println!("{}", interpreter.program.strings.get_ref(sid));
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
