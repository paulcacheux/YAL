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
        ret_ty: ty::Type,
        params: &[String],
        name: &str,
        span: Span,
        is_extern: bool,
    ) -> io::Result<()> {
        let ret_ty_str = self.ty_to_string(ret_ty);
        writeln_pp!(
            self,
            "{}{} {}({}) // {:?}",
            if is_extern { "extern " } else { "" },
            ret_ty_str,
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
            .map(|&ty| self.ty_to_string(ty))
            .collect();
        self.pp_func_header(
            exfunc.ty.return_ty,
            &params,
            &exfunc.name,
            exfunc.span,
            true,
        )
    }

    pub fn pp_function(&mut self, func: &ir::Function) -> io::Result<()> {
        let params: Vec<_> = func.parameters
            .iter()
            .map(|&(ty, id)| self.ty_to_string(ty) + " " + &idid_to_string(id))
            .collect();
        self.pp_func_header(func.return_ty, &params, &func.name, func.span, false)?;

        for decl in &func.var_declarations {
            self.pp_var_decl(decl)?;
        }

        self.pp_block_statement(&func.body)?;
        writeln_pp!(self)
    }

    pub fn pp_var_decl(&mut self, vardecl: &ir::VarDeclaration) -> io::Result<()> {
        let ty_str = self.ty_to_string(vardecl.ty);
        writeln_pp!(self, "let {}: {};", idid_to_string(vardecl.id), ty_str)
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

    pub fn pp_expression_percent(&mut self, expr: &ir::Expression) -> io::Result<String> {
        if let ir::Expression::Identifier(id) = *expr {
            Ok(idid_to_string(id))
        } else {
            Ok(format!("%{}", self.pp_expression(expr)?))
        }
    }

    pub fn pp_expression(&mut self, expr: &ir::Expression) -> io::Result<usize> {
        let rhs = match *expr {
            ir::Expression::Block(ref block) => self.pp_block_expression(block)?,
            ir::Expression::LValueToRValue(ref sub) => {
                let sub = self.pp_expression_percent(sub)?;
                format!("deref({})", sub)
            }
            ir::Expression::RValueToLValue(ref sub) => {
                let sub = self.pp_expression_percent(sub)?;
                format!("rvalue2lvalue({})", sub)
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
            ir::Expression::BitCast { dest_ty, ref sub } => {
                let sub = self.pp_expression_percent(sub)?;
                format!("bitcast {} to {}", sub, self.ty_to_string(dest_ty))
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
        };

        let id = self.new_expr();
        writeln_pp!(self, "%{} = {};", id, rhs)?;
        Ok(id)
    }

    pub fn pp_expression_as_block(&mut self, expr: &ir::Expression) -> io::Result<()> {
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

    fn ty_to_string(&self, ty: ty::Type) -> String {
        match *ty {
            ty::TypeValue::Incomplete => "incomplete".to_string(),
            ty::TypeValue::Int => "int".to_string(),
            ty::TypeValue::Double => "double".to_string(),
            ty::TypeValue::Boolean => "boolean".to_string(),
            ty::TypeValue::String => "string".to_string(),
            ty::TypeValue::Void => "void".to_string(),
            ty::TypeValue::LValue(sub) => format!("&{}", self.ty_to_string(sub)),
            ty::TypeValue::Pointer(sub) => format!("*{}", self.ty_to_string(sub)),
            ty::TypeValue::Struct(ref s) => format!("struct {}", s.name),
        }
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
