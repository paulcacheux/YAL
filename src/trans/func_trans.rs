use trans::*;
use codemap::Span;

#[derive(Debug)]
pub(super) struct FunctionBuilder<'ctxt> {
    tables: &'ctxt mut tables::Tables,
    ret_ty: ty::Type,
    in_loop: bool,
    pub var_declarations: Vec<ir::VarDeclaration>,
}

impl<'ctxt> FunctionBuilder<'ctxt> {
    pub(super) fn new(tables: &'ctxt mut tables::Tables, ret_ty: ty::Type) -> Self {
        FunctionBuilder {
            tables,
            ret_ty,
            in_loop: false,
            var_declarations: Vec::new(),
        }
    }

    pub(super) fn register_temp_local(&mut self, ty: ty::Type) -> ir::IdentifierId {
        let id = self.tables.locals.new_identifier_id();
        self.var_declarations.push(ir::VarDeclaration { ty, id });
        id
    }

    pub(super) fn translate_type(
        &mut self,
        ty: Spanned<ast::Type>,
        void: bool,
    ) -> TranslationResult<ty::Type> {
        translate_type(&mut self.tables.types, ty, void)
    }

    pub(super) fn translate_block_statement(
        &mut self,
        block: ast::BlockStatement,
    ) -> TranslationResult<ir::BlockStatement> {
        self.tables.locals.begin_scope();

        let mut ir_block = Vec::new();
        for stmt in block.statements {
            ir_block.push(self.translate_statement(stmt)?);
        }

        self.tables.locals.end_scope();
        Ok(ir_block)
    }

    pub(super) fn translate_statement_as_block(
        &mut self,
        statement: Spanned<ast::Statement>,
    ) -> TranslationResult<ir::BlockStatement> {
        let ir_stmt = self.translate_statement(statement)?;
        if let ir::Statement::Block(block) = ir_stmt {
            Ok(block)
        } else {
            Ok(vec![ir_stmt])
        }
    }

    pub(super) fn translate_var_decl(
        &mut self,
        ty: Option<Spanned<ast::Type>>,
        name: String,
        value: Spanned<ast::Expression>,
        error_span: Span,
    ) -> TranslationResult<ir::Statement> {
        // first compute the rhs to avoir local shadowing

        let value_span = value.span;
        let rhs = self.translate_expression(value)?;
        let rhs = utils::lvalue_to_rvalue(rhs);
        if let Some(ty) = ty {
            let ty = self.translate_type(ty, false)?;
            utils::check_eq_types(rhs.ty, ty, value_span)?;
        }

        if let Some(id) = self.tables.locals.register_local(name.clone(), rhs.ty) {
            self.var_declarations
                .push(ir::VarDeclaration { ty: rhs.ty, id });
            Ok(ir::Statement::Expression(utils::build_assign_to_id(
                id,
                rhs.expr,
            )))
        } else {
            error!(TranslationError::LocalAlreadyDefined(name), error_span)
        }
    }

    pub(super) fn translate_statement(
        &mut self,
        statement: Spanned<ast::Statement>,
    ) -> TranslationResult<ir::Statement> {
        let Spanned {
            inner: statement,
            span: stmt_span,
        } = statement;
        match statement {
            ast::Statement::Empty => Ok(ir::Statement::Block(vec![])),
            ast::Statement::Block(block) => {
                let block = self.translate_block_statement(block)?;
                Ok(ir::Statement::Block(block))
            }
            ast::Statement::Let(ast::LetStatement { ty, name, value }) => {
                self.translate_var_decl(ty, name, value, stmt_span)
            }
            ast::Statement::If(ast::IfStatement {
                condition,
                body,
                else_clause,
            }) => {
                let condition_span = condition.span;
                let condition = self.translate_expression(condition)?;
                let condition = utils::lvalue_to_rvalue(condition);
                utils::check_expect_type(
                    self.tables.types.get_boolean_ty(),
                    condition.ty,
                    condition_span,
                )?;

                let body = self.translate_statement_as_block(*body)?;

                let else_clause = if let Some(stmt) = else_clause {
                    self.translate_statement_as_block(*stmt)?
                } else {
                    ir::BlockStatement::new()
                };

                Ok(ir::Statement::If {
                    condition: condition.expr,
                    body,
                    else_clause,
                })
            }
            ast::Statement::While(ast::WhileStatement { condition, body }) => {
                let fake_ast_for = ast::ForStatement {
                    init: Box::new(Spanned::new(ast::Statement::Empty, Span::dummy())),
                    condition,
                    step: None,
                    body,
                };

                let spanned = Spanned::new(ast::Statement::For(fake_ast_for), stmt_span);
                self.translate_statement(spanned)
            }
            ast::Statement::For(ast::ForStatement {
                init,
                condition,
                step,
                body,
            }) => {
                let init = Box::new(self.translate_statement(*init)?);

                let condition_span = condition.span;
                let condition = self.translate_expression(condition)?;
                let condition = utils::lvalue_to_rvalue(condition);
                utils::check_expect_type(
                    self.tables.types.get_boolean_ty(),
                    condition.ty,
                    condition_span,
                )?;

                let step = if let Some(step) = step {
                    Some(self.translate_expression(step)?.expr)
                } else {
                    None
                };

                let old_in_loop = self.in_loop;
                self.in_loop = true;
                let body = self.translate_statement_as_block(*body)?;
                self.in_loop = old_in_loop;

                Ok(ir::Statement::For {
                    init,
                    condition: condition.expr,
                    step,
                    body,
                })
            }
            ast::Statement::Return(maybe_expr) => {
                let expr = if let Some(expr) = maybe_expr {
                    let expr_span = expr.span;
                    let expr = self.translate_expression(expr)?;
                    let expr = utils::lvalue_to_rvalue(expr);
                    utils::check_eq_types(expr.ty, self.ret_ty, expr_span)?;

                    Some(expr.expr)
                } else {
                    utils::check_eq_types(self.tables.types.get_void_ty(), self.ret_ty, stmt_span)?;
                    None
                };

                Ok(ir::Statement::Return(expr))
            }
            ast::Statement::Expression(expr) => {
                let expr = self.translate_expression(expr)?;
                let expr = utils::lvalue_to_rvalue(expr);
                Ok(ir::Statement::Expression(expr.expr))
            }
            ast::Statement::Break => {
                if self.in_loop {
                    Ok(ir::Statement::Break)
                } else {
                    error!(TranslationError::BreakContinueOutOfLoop, stmt_span)
                }
            }
            ast::Statement::Continue => {
                if self.in_loop {
                    Ok(ir::Statement::Continue)
                } else {
                    error!(TranslationError::BreakContinueOutOfLoop, stmt_span)
                }
            }
        }
    }

    pub(super) fn translate_expression(
        &mut self,
        expression: Spanned<ast::Expression>,
    ) -> TranslationResult<utils::TypedExpression> {
        let Spanned {
            inner: expression,
            span: expr_span,
        } = expression;

        match expression {
            ast::Expression::Literal(lit) => {
                let ty = lit.get_type(&self.tables.types);
                Ok(utils::TypedExpression {
                    ty,
                    expr: ir::Expression::Literal(lit),
                })
            }
            ast::Expression::Identifier(id) => {
                if let Some(symbol) = self.tables.locals.lookup_local(&id) {
                    let lvalue_ty = self.tables.types.lvalue_of(symbol.ty);
                    Ok(utils::TypedExpression {
                        ty: lvalue_ty,
                        expr: ir::Expression::Identifier(symbol.id),
                    })
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

                if let ty::TypeValue::LValue(sub) = *lhs.ty {
                    utils::check_eq_types(sub, rhs.ty, expr_span)?;
                } else {
                    return error!(TranslationError::NonLValueAssign, lhs_span);
                }

                Ok(utils::TypedExpression {
                    ty: rhs.ty,
                    expr: ir::Expression::Assign {
                        lhs: Box::new(lhs.expr),
                        rhs: Box::new(rhs.expr),
                    },
                })
            }
            ast::Expression::BinaryOperator { binop, lhs, rhs } => {
                let lhs = self.translate_expression(*lhs)?;
                let lhs = utils::lvalue_to_rvalue(lhs);
                let rhs = self.translate_expression(*rhs)?;
                let rhs = utils::lvalue_to_rvalue(rhs);

                if let Some((ty, op)) =
                    typeck::binop_typeck(&self.tables.types, binop, lhs.ty, rhs.ty)
                {
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

                if let Some((ty, op)) = typeck::unop_typeck(&mut self.tables.types, unop, sub.ty) {
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

                if let ty::TypeValue::LValue(sub_ty) = *sub.ty {
                    if let Some((ty, op)) =
                        typeck::lvalue_unop_typeck(&mut self.tables.types, lvalue_unop, sub_ty)
                    {
                        let expr = ir::Expression::LValueUnaryOperator {
                            lvalue_unop: op,
                            sub: Box::new(sub.expr),
                        };
                        Ok(utils::TypedExpression { ty, expr })
                    } else {
                        error!(
                            TranslationError::LValueUnOpUndefined(lvalue_unop, sub_ty),
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

                let as_ty = self.translate_type(as_ty, false)?;

                match typeck::cast_typeck(sub.ty, as_ty) {
                    typeck::CastTypeckResult::Cast(kind) => {
                        let expr = ir::Expression::Cast {
                            kind,
                            sub: Box::new(sub.expr),
                        };
                        Ok(utils::TypedExpression { ty: as_ty, expr })
                    }
                    typeck::CastTypeckResult::BitCast => {
                        let expr = ir::Expression::BitCast {
                            dest_ty: as_ty,
                            sub: Box::new(sub.expr),
                        };
                        Ok(utils::TypedExpression { ty: as_ty, expr })
                    }
                    typeck::CastTypeckResult::Error => {
                        error!(TranslationError::CastUndefined(sub.ty, as_ty), expr_span)
                    }
                }
            }
            ast::Expression::Subscript { array, index } => self.translate_subscript(*array, *index),
            ast::Expression::FunctionCall { function, args } => {
                if let Some(func_ty) = self.tables.globals.lookup_function(&function).cloned() {
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
                            utils::check_eq_types(arg.ty, func_ty.parameters_ty[index], arg_span)?;
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

    pub(super) fn translate_subscript(
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
        let array_ty = array.ty;

        let (sub_ty, ptr) = if let Some(s) = utils::unsure_subscriptable(array) {
            s
        } else {
            return error!(TranslationError::SubscriptNotArray(array_ty), array_span);
        };

        utils::check_eq_types(self.tables.types.get_int_ty(), index.ty, index_span)?;

        Ok(utils::TypedExpression {
            ty: sub_ty,
            expr: ir::Expression::UnaryOperator {
                unop: ir::UnaryOperatorKind::PointerDeref,
                sub: Box::new(ir::Expression::BinaryOperator {
                    binop: ir::BinaryOperatorKind::PtrPlusOffset,
                    lhs: Box::new(ptr),
                    rhs: Box::new(index.expr),
                }),
            },
        })
    }

    pub(super) fn translate_lazyop(
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

        let bool_ty = self.tables.types.get_boolean_ty();
        if lhs.ty != bool_ty || rhs.ty != bool_ty {
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

        let res_id = self.register_temp_local(bool_ty);
        let lvalue_bool = self.tables.types.lvalue_of(bool_ty);
        let res_id_expr = utils::TypedExpression {
            ty: lvalue_bool,
            expr: ir::Expression::Identifier(res_id),
        };

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
            ty: bool_ty,
            expr: ir::Expression::Block(Box::new(ir::BlockExpression {
                stmts,
                final_expr: utils::lvalue_to_rvalue(res_id_expr).expr,
            })),
        })
    }
}
