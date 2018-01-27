use std::io;
use std::io::Write;

use ir;
use ty;
use codemap::Span;

#[derive(Debug)]
pub struct PrettyPrinter<'w, W: Write + 'w> {
    writer: &'w mut W,
    expr_counter: usize,
    tab: usize,
}

macro_rules! writeln_pp {
    ($self:expr) => {
        writeln!($self.writer)
    };
    ($self:expr, $fmt:tt) => {
        writeln!($self.writer, concat!("{}", $fmt), "    ".repeat($self.tab))
    };
    ($self:expr, $fmt:tt, $($arg:tt)*) => {
        writeln!($self.writer, concat!("{}", $fmt), "    ".repeat($self.tab), $($arg)*)
    }
}

impl<'w, W: Write + 'w> PrettyPrinter<'w, W> {
    pub fn new(writer: &'w mut W) -> Self {
        PrettyPrinter {
            writer,
            expr_counter: 0,
            tab: 0,
        }
    }

    fn new_expr(&mut self) -> usize {
        let id = self.expr_counter;
        self.expr_counter += 1;
        id
    }

    pub fn pp_program(&mut self, program: &ir::Program) -> io::Result<()> {
        for decl in &program.declarations {
            self.expr_counter = 0;
            self.pp_declaration(decl)?;
        }
        Ok(())
    }

    pub fn pp_declaration(&mut self, decl: &ir::Declaration) -> io::Result<()> {
        match *decl {
            ir::Declaration::ExternFunction(ref exfunc) => self.pp_ex_function(exfunc),
            ir::Declaration::Function(ref func) => self.pp_function(func),
        }
    }

    fn pp_func_header(
        &mut self,
        ret_ty: &ty::Type,
        params: &[String],
        name: &str,
        span: Span,
        is_extern: bool,
    ) -> io::Result<()> {
        writeln_pp!(
            self,
            "{}{} {}({}) // {:?}",
            if is_extern { "extern " } else { "" },
            ty_to_string(&ret_ty),
            name,
            params.join(", "),
            span
        )
    }

    pub fn pp_ex_function(&mut self, exfunc: &ir::ExternFunction) -> io::Result<()> {
        let params: Vec<_> = exfunc
            .ty
            .parameters_ty
            .iter()
            .map(|ty| ty_to_string(ty))
            .collect();
        self.pp_func_header(
            &exfunc.ty.return_ty,
            &params,
            &exfunc.name,
            exfunc.span,
            true,
        )
    }

    pub fn pp_function(&mut self, func: &ir::Function) -> io::Result<()> {
        let params: Vec<_> = func.parameters
            .iter()
            .map(|&(ref ty, id)| ty_to_string(ty) + " " + &idid_to_string(id))
            .collect();
        self.pp_func_header(&func.return_ty, &params, &func.name, func.span, false)?;
        self.pp_block_statement(&func.body)?;
        writeln_pp!(self)
    }

    pub fn pp_block_statement(&mut self, block: &[ir::Statement]) -> io::Result<()> {
        writeln_pp!(self, "{{")?;
        self.tab += 1;
        for stmt in block {
            self.pp_statement(stmt)?;
        }
        self.tab -= 1;
        writeln_pp!(self, "}}")
    }

    pub fn pp_statement(&mut self, stmt: &ir::Statement) -> io::Result<()> {
        match *stmt {
            ir::Statement::Block(ref b) => self.pp_block_statement(b),
            ir::Statement::VarDecl {
                ref ty,
                id,
                ref init,
            } => {
                let init = if let Some(ref init) = *init {
                    self.pp_expression_percent(init)?
                } else {
                    "def".to_string()
                };
                writeln_pp!(
                    self,
                    "let {}: {} = {};",
                    idid_to_string(id),
                    ty_to_string(ty),
                    init
                )
            }
            ir::Statement::If {
                ref condition,
                ref body,
                ref else_clause,
            } => {
                writeln_pp!(self, "if")?;
                self.pp_expression_as_block(condition)?;
                self.pp_block_statement(body)?;
                if !else_clause.is_empty() {
                    writeln_pp!(self, "else")?;
                    self.pp_block_statement(else_clause)?;
                }
                Ok(())
            }
            ir::Statement::While {
                ref condition,
                ref body,
            } => {
                writeln_pp!(self, "while")?;
                self.pp_expression_as_block(condition)?;
                self.pp_block_statement(body)
            }
            ir::Statement::Return(ref expr) => {
                if let Some(ref expr) = *expr {
                    let expr = self.pp_expression_percent(expr)?;
                    writeln_pp!(self, "return {};", expr)
                } else {
                    writeln_pp!(self, "return;")
                }
            }
            ir::Statement::Expression(ref expr) => self.pp_expression(expr).map(|_| ()),
            ir::Statement::Break => writeln_pp!(self, "break"),
            ir::Statement::Continue => writeln_pp!(self, "continue"),
        }
    }

    pub fn pp_expression_percent(&mut self, expr: &ir::TypedExpression) -> io::Result<String> {
        if let ir::Expression::Identifier(id) = expr.expr {
            Ok(idid_to_string(id))
        } else {
            Ok(format!("%{}", self.pp_expression(expr)?))
        }
    }

    pub fn pp_expression(&mut self, expr: &ir::TypedExpression) -> io::Result<usize> {
        let ir::TypedExpression { ref ty, ref expr } = *expr;
        let rhs = match *expr {
            ir::Expression::LValueToRValue(ref sub) => {
                let sub = self.pp_expression_percent(sub)?;
                format!("deref({})", sub)
            }
            ir::Expression::Literal(ref lit) => lit_to_string(lit),
            ir::Expression::Identifier(id) => idid_to_string(id),
            ir::Expression::Assign { ref lhs, ref rhs } => {
                let lhs = self.pp_expression_percent(lhs)?;
                let rhs = self.pp_expression_percent(rhs)?;
                format!("{} -> {}", rhs, lhs)
            }
            ir::Expression::BinaryOperator {
                binop,
                ref lhs,
                ref rhs,
            } => {
                let lhs = self.pp_expression_percent(lhs)?;
                let rhs = self.pp_expression_percent(rhs)?;
                format!("{:?}({}, {})", binop, lhs, rhs)
            }
            ir::Expression::UnaryOperator { unop, ref sub } => {
                let sub = self.pp_expression_percent(sub)?;
                format!("{:?}({})", unop, sub)
            }
            ir::Expression::LValueUnaryOperator {
                lvalue_unop,
                ref sub,
            } => {
                let sub = self.pp_expression_percent(sub)?;
                format!("{:?}({})", lvalue_unop, sub)
            }
            ir::Expression::Cast { kind, ref sub } => {
                let sub = self.pp_expression_percent(sub)?;
                format!("{:?}({})", kind, sub)
            }
            ir::Expression::FunctionCall {
                ref function,
                ref args,
            } => {
                let args: Result<Vec<_>, _> = args.iter()
                    .map(|arg| self.pp_expression_percent(arg))
                    .collect();
                let args = args?;

                format!("call {}({})", function, args.join(", "))
            }
            ir::Expression::Subscript {
                ref array,
                ref index,
            } => {
                let array = self.pp_expression_percent(array)?;
                let index = self.pp_expression_percent(index)?;

                format!("subscript {}[{}]", array, index)
            }
            ir::Expression::NewArray {
                ref sub_ty,
                ref size,
            } => {
                let size = self.pp_expression_percent(size)?;
                format!("new_array {} [{}]", ty_to_string(sub_ty), size)
            }
            ir::Expression::ArrayLength(ref sub) => {
                let sub = self.pp_expression_percent(sub)?;
                format!("len {}", sub)
            }
            ir::Expression::Block(ref block) => self.pp_block_expression(block)?,
        };

        let id = self.new_expr();
        writeln_pp!(self, "%{}: {} = {};", id, ty_to_string(ty), rhs)?;
        Ok(id)
    }

    pub fn pp_expression_as_block(&mut self, expr: &ir::TypedExpression) -> io::Result<()> {
        writeln_pp!(self, "{{")?;
        self.tab += 1;
        let res = self.pp_expression_percent(expr)?;
        self.tab -= 1;
        writeln_pp!(self, "}} => {}", res)
    }

    pub fn pp_block_expression(&mut self, block: &ir::BlockExpression) -> io::Result<String> {
        writeln_pp!(self, "{{")?;
        self.tab += 1;
        for stmt in &block.stmts {
            self.pp_statement(stmt)?;
        }
        let res = self.pp_expression_percent(&block.final_expr)?;
        self.tab -= 1;
        writeln_pp!(self, "}} => {}", res)?;
        Ok(res)
    }
}

fn lit_to_string(lit: &ir::Literal) -> String {
    match *lit {
        ir::Literal::IntLiteral(i) => i.to_string(),
        ir::Literal::DoubleLiteral(d) => d.to_string(),
        ir::Literal::BooleanLiteral(b) => b.to_string(),
        ir::Literal::StringLiteral(id) => format!("{:?}", id),
    }
}

fn idid_to_string(ir::IdentifierId(id): ir::IdentifierId) -> String {
    format!("@{}", id)
}

fn ty_to_string(ty: &ty::Type) -> String {
    match *ty {
        ty::Type::Int => "int".to_string(),
        ty::Type::Double => "double".to_string(),
        ty::Type::Boolean => "boolean".to_string(),
        ty::Type::String => "string".to_string(),
        ty::Type::Void => "void".to_string(),
        ty::Type::LValue(ref sub) => format!("&{}", ty_to_string(sub)),
        ty::Type::Array(ref sub) => format!("{}[]", ty_to_string(sub)),
        ty::Type::Pointer(ref sub) => format!("{}*", ty_to_string(sub)),
        _ => unimplemented!(),
    }
}
