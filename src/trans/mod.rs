use ast;
use ty;
use ir;
use common;
use codemap::*;
use errors::TranslationError;

mod symbol_table;
#[macro_use]
mod utils;
mod typeck;
use self::symbol_table::{GlobalsTable, SymbolTable};

pub type TranslationResult<T> = Result<T, Spanned<TranslationError>>;

pub fn translate_program(
    program: ast::Program,
    runtime: Option<ir::Program>,
) -> TranslationResult<ir::Program> {
    let mut globals_table = GlobalsTable::new();

    let mut declarations = if let Some(runtime) = runtime {
        for decl in &runtime.declarations {
            let (name, fty) = match *decl {
                ir::Declaration::ExternFunction(ref exfunc) => {
                    (exfunc.name.clone(), exfunc.ty.clone())
                }
                ir::Declaration::Function(ref func) => (func.name.clone(), func.get_type()),
            };
            globals_table.register_function(name, fty);
        }

        runtime.declarations
    } else {
        Vec::new()
    };

    declarations.reserve(program.declarations.len());

    // pre translation
    for decl in &program.declarations {
        match *decl {
            ast::Declaration::Typedef(_) => unimplemented!(),
            ast::Declaration::Struct(_) => unimplemented!(),
            ast::Declaration::ExternFunction(ref exfunc) => {
                let func_ty = exfunc.get_type();
                if globals_table.register_function(exfunc.name.clone(), func_ty.clone()) {
                    return error!(
                        TranslationError::FunctionAlreadyDefined(exfunc.name.clone()),
                        exfunc.span
                    );
                }

                declarations.push(ir::Declaration::ExternFunction(ir::ExternFunction {
                    ty: func_ty,
                    name: exfunc.name.clone(),
                    span: exfunc.span,
                }));
            }
            ast::Declaration::Function(ref func) => {
                if globals_table.register_function(func.name.clone(), func.get_type()) {
                    return error!(
                        TranslationError::FunctionAlreadyDefined(func.name.clone()),
                        func.span
                    );
                }
            }
        }
    }

    for decl in program.declarations {
        match decl {
            ast::Declaration::Typedef(_) => unimplemented!(),
            ast::Declaration::Struct(_) => unimplemented!(),
            ast::Declaration::ExternFunction(_) => {} // already done
            ast::Declaration::Function(func) => declarations.push(ir::Declaration::Function(
                translate_function(&globals_table, func)?,
            )),
        }
    }

    Ok(ir::Program { declarations })
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

    let mut func_builder = FunctionBuilder::new(function.return_ty.clone());
    let mut body = func_builder.translate_block_statement(&mut symbol_table, function.body)?;

    if !utils::check_return_paths(&body) {
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
        var_declarations: func_builder.var_declarations,
        body,
        span: function.span,
    })
}

#[derive(Debug)]
struct FunctionBuilder {
    ret_ty: ty::Type,
    in_loop: bool,
    var_declarations: Vec<ir::VarDeclaration>,
}

impl FunctionBuilder {
    fn new(ret_ty: ty::Type) -> Self {
        FunctionBuilder {
            ret_ty,
            in_loop: false,
            var_declarations: Vec::new(),
        }
    }

    fn translate_block_statement(
        &mut self,
        st: &mut SymbolTable,
        block: ast::BlockStatement,
    ) -> TranslationResult<ir::BlockStatement> {
        st.begin_scope();

        let block = {
            let mut builder = BlockBuilder::new(st, self);

            for stmt in block.statements {
                builder.translate_statement(stmt)?;
            }

            builder.collect()
        };

        st.end_scope();
        Ok(block)
    }
}

#[derive(Debug)]
struct BlockBuilder<'a, 'b: 'a, 'c> {
    symbol_table: &'a mut SymbolTable<'b>,
    statements: ir::BlockStatement,
    func_builder: &'c mut FunctionBuilder,
}

impl<'a, 'b: 'a, 'c> BlockBuilder<'a, 'b, 'c> {
    fn new(st: &'a mut SymbolTable<'b>, fb: &'c mut FunctionBuilder) -> Self {
        BlockBuilder {
            symbol_table: st,
            statements: Vec::new(),
            func_builder: fb,
        }
    }

    fn collect(self) -> ir::BlockStatement {
        self.statements
    }

    fn register_temp_local(&mut self, ty: ty::Type) -> ir::IdentifierId {
        let id = self.symbol_table.new_identifier_id();
        self.func_builder
            .var_declarations
            .push(ir::VarDeclaration { ty, id });
        id
    }

    fn translate_statement_as_block(
        &mut self,
        statement: Spanned<ast::Statement>,
    ) -> TranslationResult<ir::BlockStatement> {
        match statement.inner {
            ast::Statement::Empty => Ok(ir::BlockStatement::new()),
            ast::Statement::Block(b) => self.func_builder
                .translate_block_statement(self.symbol_table, b),
            other => self.func_builder.translate_block_statement(
                self.symbol_table,
                ast::BlockStatement::from_vec(vec![Spanned::new(other, statement.span)]),
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
        let rhs = if let Some(value) = value {
            let value_span = value.span;
            let expr = self.translate_expression(value)?;
            let expr = utils::lvalue_to_rvalue(expr);
            utils::check_eq_types(&expr.ty, &ty, value_span)?;
            expr
        } else if ty.has_default_value() {
            utils::default_value_for_ty(&ty)
        } else {
            return error!(TranslationError::NoDefaultValue, error_span);
        };

        if let Some(id) = self.symbol_table.register_local(name.clone(), ty.clone()) {
            self.func_builder
                .var_declarations
                .push(ir::VarDeclaration { ty, id });
            self.statements
                .push(ir::Statement::Expression(utils::build_assign_to_id(
                    id,
                    rhs.expr,
                )))
        } else {
            return error!(TranslationError::LocalAlreadyDefined(name), error_span);
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
                let block = self.func_builder
                    .translate_block_statement(self.symbol_table, block)?;
                self.statements.push(ir::Statement::Block(block));
            }
            ast::Statement::Let(ast::LetStatement { ty, name, value }) => {
                self.translate_var_decl(ty, name, value, stmt_span)?
            }
            ast::Statement::If(ast::IfStatement {
                condition,
                body,
                else_clause,
            }) => {
                let condition_span = condition.span;
                let condition = self.translate_expression(condition)?;
                let condition = utils::lvalue_to_rvalue(condition);
                utils::check_expect_type(&ty::Type::Boolean, &condition.ty, condition_span)?;

                let body = self.translate_statement_as_block(*body)?;

                let else_clause = if let Some(stmt) = else_clause {
                    self.translate_statement_as_block(*stmt)?
                } else {
                    ir::BlockStatement::new()
                };

                self.statements.push(ir::Statement::If {
                    condition: condition.expr,
                    body,
                    else_clause,
                })
            }
            ast::Statement::While(ast::WhileStatement { condition, body }) => {
                let condition_span = condition.span;
                let condition = self.translate_expression(condition)?;
                let condition = utils::lvalue_to_rvalue(condition);
                utils::check_expect_type(&ty::Type::Boolean, &condition.ty, condition_span)?;

                let old_in_loop = self.func_builder.in_loop;
                self.func_builder.in_loop = true;
                let body = self.translate_statement_as_block(*body)?;
                self.func_builder.in_loop = old_in_loop;

                self.statements.push(ir::Statement::While {
                    condition: condition.expr,
                    body,
                })
            }
            ast::Statement::For(_) => unimplemented!(),
            ast::Statement::Return(maybe_expr) => {
                let expr = if let Some(expr) = maybe_expr {
                    let expr_span = expr.span;
                    let expr = self.translate_expression(expr)?;
                    let expr = utils::lvalue_to_rvalue(expr);
                    utils::check_eq_types(&expr.ty, &self.func_builder.ret_ty, expr_span)?;

                    Some(expr.expr)
                } else {
                    utils::check_eq_types(&ty::Type::Void, &self.func_builder.ret_ty, stmt_span)?;
                    None
                };

                self.statements.push(ir::Statement::Return(expr));
            }
            ast::Statement::Expression(expr) => {
                let expr = self.translate_expression(expr)?;
                let expr = utils::lvalue_to_rvalue(expr);
                self.statements.push(ir::Statement::Expression(expr.expr));
            }
            ast::Statement::Break => {
                if self.func_builder.in_loop {
                    self.statements.push(ir::Statement::Break);
                } else {
                    return error!(TranslationError::BreakContinueOutOfLoop, stmt_span);
                }
            }
            ast::Statement::Continue => {
                if self.func_builder.in_loop {
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
    ) -> TranslationResult<utils::TypedExpression> {
        let Spanned {
            inner: expression,
            span: expr_span,
        } = expression;

        match expression {
            ast::Expression::Literal(lit) => Ok(utils::literal_to_texpr(lit)),
            ast::Expression::Identifier(id) => {
                if let Some(symbol) = self.symbol_table.lookup_local(&id) {
                    Ok(utils::build_texpr_from_id(symbol.ty.clone(), symbol.id))
                } else {
                    error!(TranslationError::UndefinedLocal(id), expr_span)
                }
            }
            ast::Expression::Parenthesis(sub) => self.translate_expression(*sub),
            ast::Expression::Assign { lhs, rhs } => {
                let lhs_span = lhs.span;
                let lhs = self.translate_expression(*lhs)?;
                let rhs = self.translate_expression(*rhs)?;
                let rhs = utils::lvalue_to_rvalue(rhs);

                if let ty::Type::LValue(ref sub) = lhs.ty {
                    utils::check_eq_types(sub, &rhs.ty, expr_span)?;
                } else {
                    return error!(TranslationError::NonLValueAssign, lhs_span);
                }

                Ok(utils::build_assign(lhs, rhs))
            }
            ast::Expression::BinaryOperator { binop, lhs, rhs } => {
                let lhs = self.translate_expression(*lhs)?;
                let lhs = utils::lvalue_to_rvalue(lhs);
                let rhs = self.translate_expression(*rhs)?;
                let rhs = utils::lvalue_to_rvalue(rhs);

                if let Some((ty, op)) = typeck::binop_typeck(binop, &lhs.ty, &rhs.ty) {
                    let expr = ir::Expression::BinaryOperator {
                        binop: op,
                        lhs: Box::new(lhs.expr),
                        rhs: Box::new(rhs.expr),
                    };
                    Ok(utils::TypedExpression { ty, expr })
                } else {
                    error!(
                        TranslationError::BinOpUndefined(binop, lhs.ty, rhs.ty),
                        expr_span
                    )
                }
            }
            ast::Expression::LazyOperator { lazyop, lhs, rhs } => {
                self.translate_lazyop(lazyop, *lhs, *rhs, expr_span)
            }
            ast::Expression::UnaryOperator { unop, sub } => {
                let sub = self.translate_expression(*sub)?;
                let sub = utils::lvalue_to_rvalue(sub);

                if let Some((ty, op)) = typeck::unop_typeck(unop, &sub.ty) {
                    let expr = ir::Expression::UnaryOperator {
                        unop: op,
                        sub: Box::new(sub.expr),
                    };
                    Ok(utils::TypedExpression { ty, expr })
                } else {
                    error!(TranslationError::UnOpUndefined(unop, sub.ty), expr_span)
                }
            }
            ast::Expression::LValueUnaryOperator { lvalue_unop, sub } => {
                let sub = self.translate_expression(*sub)?;

                if let ty::Type::LValue(sub_ty) = sub.ty.clone() {
                    if let Some((ty, op)) = typeck::lvalue_unop_typeck(lvalue_unop, &sub_ty) {
                        let expr = ir::Expression::LValueUnaryOperator {
                            lvalue_unop: op,
                            sub: Box::new(sub.expr),
                        };
                        Ok(utils::TypedExpression { ty, expr })
                    } else {
                        error!(
                            TranslationError::LValueUnOpUndefined(lvalue_unop, *sub_ty),
                            expr_span
                        )
                    }
                } else {
                    // TODO can also be addressof
                    error!(TranslationError::LValueUnopNonLValue, expr_span)
                }
            }
            ast::Expression::Cast { as_ty, sub } => {
                let sub = self.translate_expression(*sub)?;
                let sub = utils::lvalue_to_rvalue(sub);

                match typeck::cast_typeck(&sub.ty, &as_ty) {
                    typeck::CastTypeckResult::Cast(kind) => {
                        let expr = ir::Expression::Cast {
                            kind,
                            sub: Box::new(sub.expr),
                        };
                        Ok(utils::TypedExpression {
                            ty: as_ty.clone(),
                            expr,
                        })
                    }
                    typeck::CastTypeckResult::BitCast => {
                        let expr = ir::Expression::BitCast {
                            dest_ty: as_ty.clone(),
                            sub: Box::new(sub.expr),
                        };
                        Ok(utils::TypedExpression {
                            ty: as_ty.clone(),
                            expr,
                        })
                    }
                    typeck::CastTypeckResult::Error => {
                        error!(TranslationError::CastUndefined(sub.ty, as_ty), expr_span)
                    }
                }
            }
            ast::Expression::Subscript { array, index } => self.translate_subscript(*array, *index),
            ast::Expression::FunctionCall { function, args } => {
                if let Some(func_ty) = self.symbol_table.lookup_function(&function).cloned() {
                    let mut args_translated = Vec::with_capacity(args.len());
                    if !func_ty.is_vararg && func_ty.parameters_ty.len() != args.len() {
                        return error!(
                            TranslationError::FunctionCallArityMismatch(
                                func_ty.parameters_ty.len(),
                                args.len(),
                            ),
                            expr_span
                        );
                    }

                    if func_ty.is_vararg && func_ty.parameters_ty.len() > args.len() {
                        return error!(
                            TranslationError::FunctionCallArityMismatch(
                                func_ty.parameters_ty.len(),
                                args.len()
                            ),
                            expr_span
                        );
                    }

                    for (index, arg) in args.into_iter().enumerate() {
                        let arg_span = arg.span;
                        let arg = self.translate_expression(arg)?;
                        let arg = utils::lvalue_to_rvalue(arg);
                        if index < func_ty.parameters_ty.len() {
                            utils::check_eq_types(
                                &arg.ty,
                                &func_ty.parameters_ty[index],
                                arg_span,
                            )?;
                        }
                        args_translated.push(arg.expr);
                    }

                    let ret_ty = func_ty.return_ty;
                    Ok(utils::TypedExpression {
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
            _ => unimplemented!(),
        }
    }

    fn translate_subscript(
        &mut self,
        array: Spanned<ast::Expression>,
        index: Spanned<ast::Expression>,
    ) -> TranslationResult<utils::TypedExpression> {
        let array_span = array.span;
        let index_span = index.span;

        let array = self.translate_expression(array)?;
        let array = utils::lvalue_to_rvalue(array);
        let index = self.translate_expression(index)?;
        let index = utils::lvalue_to_rvalue(index);
        let array_ty = array.ty.clone();

        let (sub_ty, ptr) = if let Some(s) = utils::unsure_subscriptable(array) {
            s
        } else {
            return error!(TranslationError::SubscriptNotArray(array_ty), array_span);
        };

        if index.ty != ty::Type::Int {
            return error!(
                TranslationError::UnexpectedType(ty::Type::Int, index.ty.clone()),
                index_span
            );
        }

        Ok(utils::TypedExpression {
            ty: sub_ty,
            expr: ir::Expression::Subscript {
                ptr: Box::new(ptr),
                index: Box::new(index.expr),
            },
        })
    }

    fn translate_lazyop(
        &mut self,
        lazyop: ast::LazyOperatorKind,
        lhs: Spanned<ast::Expression>,
        rhs: Spanned<ast::Expression>,
        expr_span: Span,
    ) -> TranslationResult<utils::TypedExpression> {
        let lhs = self.translate_expression(lhs)?;
        let lhs = utils::lvalue_to_rvalue(lhs);
        let rhs = self.translate_expression(rhs)?;
        let rhs = utils::lvalue_to_rvalue(rhs);

        if lhs.ty != ty::Type::Boolean || rhs.ty != ty::Type::Boolean {
            return error!(
                TranslationError::LazyOpUndefined(lazyop, lhs.ty, rhs.ty),
                expr_span
            );
        }

        let (init, cond) = match lazyop {
            ast::LazyOperatorKind::LogicalOr => {
                let init = ir::Expression::Literal(common::Literal::BooleanLiteral(true));

                let cond = ir::Expression::UnaryOperator {
                    unop: ir::UnaryOperatorKind::BooleanNot,
                    sub: Box::new(lhs.expr),
                };

                (init, cond)
            }
            ast::LazyOperatorKind::LogicalAnd => {
                let init = ir::Expression::Literal(common::Literal::BooleanLiteral(false));
                (init, lhs.expr)
            }
        };

        let res_id = self.register_temp_local(ty::Type::Boolean);
        let res_id_expr = utils::build_texpr_from_id(ty::Type::Boolean, res_id);

        let stmts = vec![
            ir::Statement::Expression(utils::build_assign_to_id(res_id, init)),
            ir::Statement::If {
                condition: cond,
                body: vec![
                    ir::Statement::Expression(utils::build_assign_to_id(res_id, rhs.expr)),
                ],
                else_clause: vec![],
            },
        ];

        Ok(utils::TypedExpression {
            ty: ty::Type::Boolean,
            expr: ir::Expression::Block(Box::new(ir::BlockExpression {
                stmts,
                final_expr: utils::lvalue_to_rvalue(res_id_expr).expr,
            })),
        })
    }
}

pub fn check_if_main_declaration(prog: &ir::Program) -> TranslationResult<()> {
    for decl in &prog.declarations {
        let (name, ty, span) = match *decl {
            ir::Declaration::ExternFunction(ref exfunc) => {
                (&exfunc.name, exfunc.ty.clone(), exfunc.span)
            }
            ir::Declaration::Function(ref func) => (&func.name, func.get_type(), func.span),
        };

        if name == "main" {
            if ty.return_ty == ty::Type::Int && ty.parameters_ty.is_empty() && !ty.is_vararg {
                return Ok(());
            } else {
                return error!(TranslationError::MainWrongType, span);
            }
        }
    }
    error!(TranslationError::NoMain, Span::dummy())
}