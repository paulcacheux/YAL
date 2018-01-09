use ast;
use ty;
use ir;
use span::*;
use errors::TranslationError;

mod symbol_table;
use self::symbol_table::{GlobalsTable, SymbolTable};

pub type TranslationResult<T> = Result<T, Spanned<TranslationError>>;

macro_rules! error {
    ($err:expr, $span:expr) => {
        Err(Spanned::new($err, $span))
    }
}

pub fn translate_program(program: ast::Program) -> TranslationResult<ir::Program> {
    let mut globals_table = GlobalsTable::new();

    globals_table.register_function(
        "printInt".to_string(),
        ty::FunctionType {
            return_ty: ty::Type::Void,
            parameters_ty: vec![ty::Type::Int],
        },
    );
    globals_table.register_function(
        "printDouble".to_string(),
        ty::FunctionType {
            return_ty: ty::Type::Void,
            parameters_ty: vec![ty::Type::Double],
        },
    );
    globals_table.register_function(
        "printString".to_string(),
        ty::FunctionType {
            return_ty: ty::Type::Void,
            parameters_ty: vec![ty::Type::String],
        },
    );

    globals_table.register_function(
        "readInt".to_string(),
        ty::FunctionType {
            return_ty: ty::Type::Int,
            parameters_ty: Vec::new(),
        },
    );
    globals_table.register_function(
        "readDouble".to_string(),
        ty::FunctionType {
            return_ty: ty::Type::Double,
            parameters_ty: Vec::new(),
        },
    );

    // pre translation
    let mut is_main_present = false;
    for decl in &program.declarations {
        match *decl {
            ast::Declaration::Typedef(_) => unimplemented!(),
            ast::Declaration::Struct(_) => unimplemented!(),
            ast::Declaration::Function(ref func) => {
                if globals_table.register_function(func.name.clone(), func.get_type()) {
                    return error!(
                        TranslationError::FunctionAlreadyDefined(func.name.clone()),
                        func.span
                    );
                }

                if func.name == "main" {
                    if func.parameters.is_empty() {
                        is_main_present = true;
                    } else {
                        return error!(TranslationError::MainWrongType, func.span);
                    }
                }
            }
        }
    }

    if !is_main_present {
        return error!(TranslationError::NoMain, Span::dummy());
    }

    let mut declarations = Vec::with_capacity(program.declarations.len());
    for decl in program.declarations {
        match decl {
            ast::Declaration::Typedef(_) => unimplemented!(),
            ast::Declaration::Struct(_) => unimplemented!(),
            ast::Declaration::Function(func) => {
                declarations.push(translate_function(&globals_table, func)?)
            }
        }
    }

    Ok(ir::Program {
        strings: program.strings,
        declarations,
    })
}

fn translate_function(
    globals: &GlobalsTable,
    function: ast::Function,
) -> TranslationResult<ir::Function> {
    let mut symbol_table = SymbolTable::new(globals);
    symbol_table.begin_scope();

    let mut parameters = Vec::with_capacity(function.parameters.len());
    for (param_ty, param_name) in function.parameters {
        if let Some(id) = symbol_table.register_local(param_name.clone(), param_ty.clone()) {
            parameters.push((param_ty, id));
        } else {
            return error!(
                TranslationError::ParameterAlreadyDefined(param_name),
                function.span
            );
        }
    }

    symbol_table.begin_scope();

    let mut func_infos = FunctionInfos::new(function.return_ty.clone());
    let mut body = translate_block_statement(&mut symbol_table, function.body, &mut func_infos)?;

    if !check_return_paths(&body) {
        if function.return_ty != ty::Type::Void {
            return error!(TranslationError::NotAllPathsReturn, function.span);
        } else {
            body.push(ir::Statement::Return(None)); // we add a return void
        }
    }

    symbol_table.end_scope();
    symbol_table.end_scope();

    Ok(ir::Function {
        return_ty: function.return_ty,
        name: function.name,
        parameters,
        body,
        span: function.span,
    })
}

fn translate_block_statement(
    st: &mut SymbolTable,
    block: ast::BlockStatement,
    fi: &mut FunctionInfos,
) -> TranslationResult<ir::BlockStatement> {
    st.begin_scope();

    let block = {
        let mut builder = BlockBuilder::new(st, fi);

        for stmt in block.statements {
            builder.translate_statement(stmt)?;
        }

        builder.collect()
    };

    st.end_scope();
    Ok(block)
}

#[derive(Debug)]
struct FunctionInfos {
    ret_ty: ty::Type,
    in_loop: bool,
}

impl FunctionInfos {
    fn new(ret_ty: ty::Type) -> Self {
        FunctionInfos {
            ret_ty,
            in_loop: false,
        }
    }
}

#[derive(Debug)]
struct BlockBuilder<'a, 'b: 'a, 'c> {
    symbol_table: &'a mut SymbolTable<'b>,
    statements: ir::BlockStatement,
    func_infos: &'c mut FunctionInfos,
}

impl<'a, 'b: 'a, 'c> BlockBuilder<'a, 'b, 'c> {
    fn new(st: &'a mut SymbolTable<'b>, fi: &'c mut FunctionInfos) -> Self {
        BlockBuilder {
            symbol_table: st,
            statements: Vec::new(),
            func_infos: fi,
        }
    }

    fn collect(self) -> ir::BlockStatement {
        self.statements
    }

    fn translate_statement_as_block(
        &mut self,
        statement: Spanned<ast::Statement>,
    ) -> TranslationResult<ir::BlockStatement> {
        match statement.inner {
            ast::Statement::Empty => Ok(ir::BlockStatement::new()),
            ast::Statement::Block(b) => {
                translate_block_statement(self.symbol_table, b, self.func_infos)
            }
            other => translate_block_statement(
                self.symbol_table,
                ast::BlockStatement::from_vec(vec![Spanned::new(other, statement.span)]),
                self.func_infos,
            ),
        }
    }

    fn translate_var_decl(
        &mut self,
        ty: ty::Type,
        name: String,
        value: Option<Spanned<ast::Expression>>,
        error_span: Span,
    ) -> TranslationResult<()> {
        // we must compute this first to avoid shadowing
        let value_expr = if let Some(value) = value {
            let value_span = value.span;
            let expr = self.translate_expression(value)?;
            let expr = lvalue_to_rvalue(expr);
            check_eq_types(&expr.ty, &ty, value_span)?;
            Some(expr)
        } else if ty.has_default_value() {
            let lit = match ty {
                ty::Type::Int => ir::Literal::IntLiteral(0),
                ty::Type::Double => ir::Literal::DoubleLiteral(0.0),
                ty::Type::Boolean => ir::Literal::BooleanLiteral(false),
                _ => unreachable!(),
            };
            Some(ir::TypedExpression {
                ty: ty.clone(),
                expr: ir::Expression::Literal(lit),
            })
        } else {
            None
        };

        let id = if let Some(id) = self.symbol_table.register_local(name.clone(), ty.clone()) {
            self.statements
                .push(ir::Statement::VarDecl { ty: ty.clone(), id });
            id
        } else {
            return error!(
                TranslationError::LocalAlreadyDefined(name),
                error_span
            );
        };

        if let Some(rhs) = value_expr {
            let lhs = ir::Expression::Identifier(id);
            let lhs = ir::TypedExpression {
                ty: ty::Type::LValue(Box::new(ty.clone())),
                expr: lhs,
            };

            let assign_expr = ir::TypedExpression {
                ty,
                expr: ir::Expression::Assign {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            };

            self.statements.push(ir::Statement::Expression(assign_expr));
        } else if !ty.has_default_value() {
            return error!(TranslationError::NoDefaultValue, error_span);
        }
        Ok(())
    }

    fn translate_statement(&mut self, statement: Spanned<ast::Statement>) -> TranslationResult<()> {
        let Spanned {
            inner: statement,
            span: stmt_span,
        } = statement;
        match statement {
            ast::Statement::Empty => {}
            ast::Statement::Block(block) => {
                let block = translate_block_statement(self.symbol_table, block, self.func_infos)?;
                self.statements.push(ir::Statement::Block(block));
            }
            ast::Statement::VarDecl(ast::VarDeclarations { ty, declarations }) => {
                for (name, value) in declarations {
                    self.translate_var_decl(ty.clone(), name, value, stmt_span)?;
                }
            }
            ast::Statement::If(ast::IfStatement {
                condition,
                body,
                else_clause,
            }) => {
                let condition_span = condition.span;
                let condition = self.translate_expression(condition)?;
                let condition = lvalue_to_rvalue(condition);
                check_eq_types(&condition.ty, &ty::Type::Boolean, condition_span)?;

                let body = self.translate_statement_as_block(*body)?;

                let else_clause = if let Some(stmt) = else_clause {
                    self.translate_statement_as_block(*stmt)?
                } else {
                    ir::BlockStatement::new()
                };

                self.statements.push(ir::Statement::If {
                    condition,
                    body,
                    else_clause,
                })
            }
            ast::Statement::While(ast::WhileStatement { condition, body }) => {
                let condition_span = condition.span;
                let condition = self.translate_expression(condition)?;
                let condition = lvalue_to_rvalue(condition);
                check_eq_types(&condition.ty, &ty::Type::Boolean, condition_span)?;

                let old_in_loop = self.func_infos.in_loop;
                self.func_infos.in_loop = true;
                let body = self.translate_statement_as_block(*body)?;
                self.func_infos.in_loop = old_in_loop;

                self.statements
                    .push(ir::Statement::While { condition, body })
            }
            ast::Statement::For(ast::ForStatement {
                ty,
                name,
                array,
                body,
            }) => {
                let array_span = array.span;
                let array = self.translate_expression(array)?;
                let array = lvalue_to_rvalue(array);

                if let ty::Type::Array(sub_ty) = array.ty.clone() {
                    check_eq_types(&sub_ty, &ty, array_span)?;
                } else {
                    return error!(TranslationError::SubscriptNotArray(array.ty), array_span);
                }

                self.symbol_table.begin_scope();
                let id = if let Some(id) = self.symbol_table.register_local(name.clone(), ty) {
                    id
                } else {
                    unreachable!()
                };

                let old_in_loop = self.func_infos.in_loop;
                self.func_infos.in_loop = true;
                let body = self.translate_statement_as_block(*body)?;
                self.func_infos.in_loop = old_in_loop;
                self.symbol_table.end_scope();

                self.statements.push(ir::Statement::For { id, array, body });
            }
            ast::Statement::Return(maybe_expr) => {
                let expr = if let Some(expr) = maybe_expr {
                    let expr_span = expr.span;
                    let expr = self.translate_expression(expr)?;
                    let expr = lvalue_to_rvalue(expr);
                    check_eq_types(&expr.ty, &self.func_infos.ret_ty, expr_span)?;

                    Some(expr)
                } else {
                    check_eq_types(&ty::Type::Void, &self.func_infos.ret_ty, stmt_span)?;
                    None
                };

                self.statements.push(ir::Statement::Return(expr));
            }
            ast::Statement::Expression(expr) => {
                let expr = self.translate_expression(expr)?;
                let expr = lvalue_to_rvalue(expr);
                self.statements.push(ir::Statement::Expression(expr));
            }
            ast::Statement::Break => {
                if self.func_infos.in_loop {
                    self.statements.push(ir::Statement::Break);
                } else {
                    return error!(TranslationError::BreakContinueOutOfLoop, stmt_span);
                }
            }
            ast::Statement::Continue => {
                if self.func_infos.in_loop {
                    self.statements.push(ir::Statement::Continue);
                } else {
                    return error!(TranslationError::BreakContinueOutOfLoop, stmt_span);
                }
            }
        }
        Ok(())
    }

    fn translate_expression(
        &mut self,
        expression: Spanned<ast::Expression>,
    ) -> TranslationResult<ir::TypedExpression> {
        let Spanned {
            inner: expression,
            span: expr_span,
        } = expression;

        match expression {
            ast::Expression::Literal(lit) => {
                let (ty, lit) = match lit {
                    ast::Literal::IntLiteral(i) => (ty::Type::Int, ir::Literal::IntLiteral(i)),
                    ast::Literal::DoubleLiteral(d) => {
                        (ty::Type::Double, ir::Literal::DoubleLiteral(d))
                    }
                    ast::Literal::BooleanLiteral(b) => {
                        (ty::Type::Boolean, ir::Literal::BooleanLiteral(b))
                    }
                    ast::Literal::StringLiteral(s) => {
                        (ty::Type::String, ir::Literal::StringLiteral(s))
                    }
                };

                Ok(ir::TypedExpression {
                    ty,
                    expr: ir::Expression::Literal(lit),
                })
            }
            ast::Expression::Identifier(id) => {
                if let Some(symbol) = self.symbol_table.lookup_local(&id) {
                    Ok(ir::TypedExpression {
                        ty: ty::Type::LValue(Box::new(symbol.ty.clone())),
                        expr: ir::Expression::Identifier(symbol.id),
                    })
                } else {
                    error!(TranslationError::UndefinedLocal(id), expr_span)
                }
            }
            ast::Expression::Assign { lhs, rhs } => {
                let lhs_span = lhs.span;
                let lhs = self.translate_expression(*lhs)?;
                let rhs = self.translate_expression(*rhs)?;
                let rhs = lvalue_to_rvalue(rhs);

                if let ty::Type::LValue(ref sub) = lhs.ty {
                    check_eq_types(sub, &rhs.ty, expr_span)?;
                } else {
                    return error!(TranslationError::NonLValueAssign, lhs_span);
                }

                let ty = rhs.ty.clone();
                let expr = ir::Expression::Assign {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok(ir::TypedExpression { ty, expr })
            }
            ast::Expression::BinaryOperator { binop, lhs, rhs } => {
                let lhs = self.translate_expression(*lhs)?;
                let lhs = lvalue_to_rvalue(lhs);
                let rhs = self.translate_expression(*rhs)?;
                let rhs = lvalue_to_rvalue(rhs);

                if let Some((ty, op)) = binop_typeck(binop, &lhs.ty, &rhs.ty) {
                    let expr = ir::Expression::BinaryOperator {
                        binop: op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    };
                    Ok(ir::TypedExpression { ty, expr })
                } else {
                    error!(
                        TranslationError::BinOpUndefined(binop, lhs.ty, rhs.ty),
                        expr_span
                    )
                }
            }
            ast::Expression::LazyOperator { lazyop, lhs, rhs } => {
                let lhs = self.translate_expression(*lhs)?;
                let lhs = lvalue_to_rvalue(lhs);
                let rhs = self.translate_expression(*rhs)?;
                let rhs = lvalue_to_rvalue(rhs);

                if let Some((ty, op)) = lazyop_typeck(lazyop, &lhs.ty, &rhs.ty) {
                    let expr = ir::Expression::LazyOperator {
                        lazyop: op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    };
                    Ok(ir::TypedExpression { ty, expr })
                } else {
                    error!(
                        TranslationError::LazyOpUndefined(lazyop, lhs.ty, rhs.ty),
                        expr_span
                    )
                }
            }
            ast::Expression::UnaryOperator { unop, sub } => {
                let sub = self.translate_expression(*sub)?;
                let sub = lvalue_to_rvalue(sub);

                if let Some((ty, op)) = unop_typeck(unop, &sub.ty) {
                    let expr = ir::Expression::UnaryOperator {
                        unop: op,
                        sub: Box::new(sub),
                    };
                    Ok(ir::TypedExpression { ty, expr })
                } else {
                    error!(TranslationError::UnOpUndefined(unop, sub.ty), expr_span)
                }
            }
            ast::Expression::Increment(sub) => {
                let sub_span = sub.span;
                let sub = self.translate_expression(*sub)?;

                if let ty::Type::LValue(ref sub_ty) = sub.ty {
                    check_eq_types(sub_ty, &ty::Type::Int, sub_span)?;
                } else {
                    return error!(TranslationError::IncDecNonLValue, sub_span);
                }

                let ty = sub.ty.clone();

                Ok(ir::TypedExpression {
                    ty,
                    expr: ir::Expression::Increment(Box::new(sub)),
                })
            }
            ast::Expression::Decrement(sub) => {
                let sub_span = sub.span;
                let sub = self.translate_expression(*sub)?;

                if let ty::Type::LValue(ref sub_ty) = sub.ty {
                    check_eq_types(sub_ty, &ty::Type::Int, sub_span)?;
                } else {
                    return error!(TranslationError::IncDecNonLValue, sub_span);
                }

                let ty = sub.ty.clone();

                Ok(ir::TypedExpression {
                    ty,
                    expr: ir::Expression::Decrement(Box::new(sub)),
                })
            }
            ast::Expression::Subscript { array, index } => {
                let index_span = index.span;
                let array = self.translate_expression(*array)?;
                let array = lvalue_to_rvalue(array);
                let index = self.translate_expression(*index)?;
                let index = lvalue_to_rvalue(index);

                if let ty::Type::Array(sub_ty) = array.ty.clone() {
                    check_eq_types(&index.ty, &ty::Type::Int, index_span)?;
                    Ok(ir::TypedExpression {
                        ty: ty::Type::LValue(sub_ty),
                        expr: ir::Expression::Subscript {
                            array: Box::new(array),
                            index: Box::new(index),
                        },
                    })
                } else {
                    error!(TranslationError::SubscriptNotArray(array.ty), expr_span)
                }
            }
            ast::Expression::FunctionCall { function, args } => {
                if let Some(func_ty) = self.symbol_table.lookup_function(&function).cloned() {
                    let mut args_translated = Vec::with_capacity(args.len());
                    if func_ty.parameters_ty.len() != args.len() {
                        return error!(
                            TranslationError::FunctionCallArity(
                                func_ty.parameters_ty.len(),
                                args.len(),
                            ),
                            expr_span
                        );
                    }

                    for (arg, param_ty) in args.into_iter().zip(func_ty.parameters_ty.iter()) {
                        let arg_span = arg.span;
                        let arg = self.translate_expression(arg)?;
                        let arg = lvalue_to_rvalue(arg);
                        check_eq_types(&arg.ty, param_ty, arg_span)?;
                        args_translated.push(arg);
                    }
                    let ret_ty = func_ty.return_ty;
                    Ok(ir::TypedExpression {
                        ty: ret_ty,
                        expr: ir::Expression::FunctionCall {
                            function,
                            args: args_translated,
                        },
                    })
                } else {
                    error!(TranslationError::FunctionUndefined(function), expr_span)
                }
            }
            ast::Expression::NewArray { ty, sizes } => {
                let mut array_ty = ty.clone();
                for _ in 0..sizes.len() {
                    array_ty = ty::Type::Array(Box::new(array_ty));
                }

                let mut new_sizes = Vec::with_capacity(sizes.len());
                for size in sizes {
                    let size_span = size.span;
                    let size = self.translate_expression(size)?;
                    let size = lvalue_to_rvalue(size);

                    check_eq_types(&ty::Type::Int, &size.ty, size_span)?;
                    new_sizes.push(size);
                }

                Ok(ir::TypedExpression {
                    ty: array_ty,
                    expr: ir::Expression::NewArray {
                        base_ty: ty,
                        sizes: new_sizes,
                    },
                })
            }
            ast::Expression::MemberAccess { expr, member } => {
                // TODO change this. It currently only works for .length on arrays
                let expr = self.translate_expression(*expr)?;
                let expr = lvalue_to_rvalue(expr);

                if member != "length" {
                    return error!(TranslationError::MemberUndefined, expr_span);
                }

                if let ty::Type::Array(_) = expr.ty {
                    Ok(ir::TypedExpression {
                        ty: ty::Type::Int,
                        expr: ir::Expression::ArrayLength(Box::new(expr)),
                    })
                } else {
                    // TODO change the error
                    error!(TranslationError::LengthOnNonArray(expr.ty), expr_span)
                }
            }
        }
    }
}

fn lvalue_to_rvalue(expression: ir::TypedExpression) -> ir::TypedExpression {
    match expression.ty.clone() {
        ty::Type::LValue(sub) => ir::TypedExpression {
            ty: *sub,
            expr: ir::Expression::LValueToRValue(Box::new(expression)),
        },
        other => ir::TypedExpression {
            ty: other,
            expr: expression.expr,
        },
    }
}

fn binop_typeck(
    binop: ast::BinaryOperatorKind,
    lhs: &ty::Type,
    rhs: &ty::Type,
) -> Option<(ty::Type, ir::BinaryOperatorKind)> {
    use ast::BinaryOperatorKind::*;
    match (binop, lhs, rhs) {
        (Plus, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntPlus))
        }
        (Plus, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Double, ir::BinaryOperatorKind::DoublePlus))
        }
        (Minus, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntMinus))
        }
        (Minus, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Double, ir::BinaryOperatorKind::DoubleMinus))
        }
        (Multiply, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntMultiply))
        }
        (Multiply, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Double, ir::BinaryOperatorKind::DoubleMultiply))
        }
        (Divide, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntDivide))
        }
        (Divide, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Double, ir::BinaryOperatorKind::DoubleDivide))
        }
        (Modulo, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntModulo))
        }

        (Equal, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntEqual))
        }
        (Equal, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleEqual))
        }
        (Equal, &ty::Type::Boolean, &ty::Type::Boolean) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::BooleanEqual))
        }

        (NotEqual, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntNotEqual))
        }
        (NotEqual, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleNotEqual))
        }
        (NotEqual, &ty::Type::Boolean, &ty::Type::Boolean) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::BooleanNotEqual))
        }

        (Less, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntLess))
        }
        (Less, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleLess))
        }

        (LessEqual, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntLessEqual))
        }
        (LessEqual, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleLessEqual))
        }

        (Greater, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntGreater))
        }
        (Greater, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleGreater))
        }

        (GreaterEqual, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntGreaterEqual))
        }
        (GreaterEqual, &ty::Type::Double, &ty::Type::Double) => Some((
            ty::Type::Boolean,
            ir::BinaryOperatorKind::DoubleGreaterEqual,
        )),

        _ => None,
    }
}

fn lazyop_typeck(
    lazyop: ast::LazyOperatorKind,
    lhs: &ty::Type,
    rhs: &ty::Type,
) -> Option<(ty::Type, ir::LazyOperatorKind)> {
    use ast::LazyOperatorKind::*;

    match (lazyop, lhs, rhs) {
        (LogicalAnd, &ty::Type::Boolean, &ty::Type::Boolean) => {
            Some((ty::Type::Boolean, ir::LazyOperatorKind::BooleanLogicalAnd))
        }
        (LogicalOr, &ty::Type::Boolean, &ty::Type::Boolean) => {
            Some((ty::Type::Boolean, ir::LazyOperatorKind::BooleanLogicalOr))
        }
        _ => None,
    }
}

fn unop_typeck(
    unop: ast::UnaryOperatorKind,
    sub: &ty::Type,
) -> Option<(ty::Type, ir::UnaryOperatorKind)> {
    use ast::UnaryOperatorKind::*;

    match (unop, sub) {
        (Minus, &ty::Type::Int) => Some((ty::Type::Int, ir::UnaryOperatorKind::IntMinus)),
        (Minus, &ty::Type::Double) => Some((ty::Type::Double, ir::UnaryOperatorKind::DoubleMinus)),
        (LogicalNot, &ty::Type::Boolean) => {
            Some((ty::Type::Boolean, ir::UnaryOperatorKind::BooleanNot))
        }
        _ => None,
    }
}

fn check_return_paths(block: &[ir::Statement]) -> bool {
    block.iter().map(check_return_paths_stmt).any(|b| b)
}

fn check_return_paths_stmt(stmt: &ir::Statement) -> bool {
    match *stmt {
        ir::Statement::Block(ref b) => check_return_paths(b),
        ir::Statement::If {
            ref condition,
            ref body,
            ref else_clause,
        } => match condition.expr {
            ir::Expression::Literal(ir::Literal::BooleanLiteral(true)) => check_return_paths(body),
            ir::Expression::Literal(ir::Literal::BooleanLiteral(false)) => {
                check_return_paths(else_clause)
            }
            _ => check_return_paths(body) && check_return_paths(else_clause),
        },
        ir::Statement::While { ref condition, .. } => {
            if let ir::Expression::Literal(ir::Literal::BooleanLiteral(true)) = condition.expr {
                true
            } else {
                false
            }
        }
        ir::Statement::Return(_) => true,
        _ => false,
    }
}

fn check_eq_types(a: &ty::Type, b: &ty::Type, error_span: Span) -> TranslationResult<()> {
    if a != b {
        error!(
            TranslationError::MismatchingTypes(a.clone(), b.clone(),),
            error_span
        )
    } else {
        Ok(())
    }
}
