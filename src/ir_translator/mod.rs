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

    let mut func_infos = FunctionInfos::new(function.return_ty.clone());
    let mut body = translate_block_statement(&mut symbol_table, function.body, &mut func_infos)?;

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
            self.statements.push(ir::Statement::VarDecl {
                ty,
                id,
                init: Some(rhs),
            });
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
                let condition = utils::lvalue_to_rvalue(condition);
                utils::check_expect_type(&ty::Type::Boolean, &condition.ty, condition_span)?;

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
                let condition = utils::lvalue_to_rvalue(condition);
                utils::check_expect_type(&ty::Type::Boolean, &condition.ty, condition_span)?;

                let old_in_loop = self.func_infos.in_loop;
                self.func_infos.in_loop = true;
                let body = self.translate_statement_as_block(*body)?;
                self.func_infos.in_loop = old_in_loop;

                self.statements
                    .push(ir::Statement::While { condition, body })
            }
            ast::Statement::For(for_stmt) => self.translate_for_statement(for_stmt)?,
            ast::Statement::Return(maybe_expr) => {
                let expr = if let Some(expr) = maybe_expr {
                    let expr_span = expr.span;
                    let expr = self.translate_expression(expr)?;
                    let expr = utils::lvalue_to_rvalue(expr);
                    utils::check_eq_types(&expr.ty, &self.func_infos.ret_ty, expr_span)?;

                    Some(expr)
                } else {
                    utils::check_eq_types(&ty::Type::Void, &self.func_infos.ret_ty, stmt_span)?;
                    None
                };

                self.statements.push(ir::Statement::Return(expr));
            }
            ast::Statement::Expression(expr) => {
                let expr = self.translate_expression(expr)?;
                let expr = utils::lvalue_to_rvalue(expr);
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

    fn translate_for_statement(&mut self, for_stmt: ast::ForStatement) -> TranslationResult<()> {
        let ast::ForStatement {
            ty,
            name,
            array,
            body,
        } = for_stmt;

        let array_span = array.span;
        let array = self.translate_expression(array)?;
        let array = utils::lvalue_to_rvalue(array);

        if let ty::Type::Array(sub_ty) = array.ty.clone() {
            utils::check_eq_types(&sub_ty, &ty, array_span)?;
        } else {
            return error!(TranslationError::SubscriptNotArray(array.ty), array_span);
        }

        // translation of stmt
        self.symbol_table.begin_scope();
        let current_id =
            if let Some(id) = self.symbol_table.register_local(name.clone(), ty.clone()) {
                id
            } else {
                unreachable!()
            };

        let old_in_loop = self.func_infos.in_loop;
        self.func_infos.in_loop = true;
        let body = self.translate_statement_as_block(*body)?;
        self.func_infos.in_loop = old_in_loop;
        self.symbol_table.end_scope();

        // loop building
        let (_, loop_block) = self.create_loop(ty.clone(), array, |array_indexed| {
            let array_indexed = utils::lvalue_to_rvalue(array_indexed);
            Ok(vec![
                ir::Statement::VarDecl {
                    ty: ty,
                    id: current_id,
                    init: Some(array_indexed),
                },
                ir::Statement::Block(body),
            ])
        })?;
        self.statements.push(ir::Statement::Block(loop_block));
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
                self.translate_lazyop(lazyop, *lhs, *rhs, expr_span)
            }
            ast::Expression::UnaryOperator { unop, sub } => {
                let sub = self.translate_expression(*sub)?;
                let sub = utils::lvalue_to_rvalue(sub);

                if let Some((ty, op)) = typeck::unop_typeck(unop, &sub.ty) {
                    let expr = ir::Expression::UnaryOperator {
                        unop: op,
                        sub: Box::new(sub),
                    };
                    Ok(ir::TypedExpression { ty, expr })
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
                            sub: Box::new(sub),
                        };
                        Ok(ir::TypedExpression { ty, expr })
                    } else {
                        error!(
                            TranslationError::LValueUnOpUndefined(lvalue_unop, *sub_ty),
                            expr_span
                        )
                    }
                } else {
                    // TODO can also be addressof
                    return error!(TranslationError::LValueUnopNonLValue, expr_span);
                }
            }
            ast::Expression::Subscript { array, index } => {
                let index_span = index.span;
                let array = self.translate_expression(*array)?;
                let array = utils::lvalue_to_rvalue(array);
                let index = self.translate_expression(*index)?;
                let index = utils::lvalue_to_rvalue(index);

                if let ty::Type::Array(sub_ty) = array.ty.clone() {
                    utils::check_eq_types(&index.ty, &ty::Type::Int, index_span)?;
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
            ast::Expression::NewArray { ty, sizes } => self.translate_new_array(ty, sizes),
            ast::Expression::MemberAccess { expr, member } => {
                // TODO change this. It currently only works for .length on arrays
                let expr = self.translate_expression(*expr)?;
                let expr = utils::lvalue_to_rvalue(expr);

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

    fn translate_lazyop(
        &mut self,
        lazyop: ast::LazyOperatorKind,
        lhs: Spanned<ast::Expression>,
        rhs: Spanned<ast::Expression>,
        expr_span: Span,
    ) -> TranslationResult<ir::TypedExpression> {
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
                let init = utils::literal_to_texpr(common::Literal::BooleanLiteral(true));

                let cond = ir::TypedExpression {
                    ty: ty::Type::Boolean,
                    expr: ir::Expression::UnaryOperator {
                        unop: ir::UnaryOperatorKind::BooleanNot,
                        sub: Box::new(lhs),
                    },
                };

                (init, cond)
            }
            ast::LazyOperatorKind::LogicalAnd => {
                let init = utils::literal_to_texpr(common::Literal::BooleanLiteral(false));
                (init, lhs)
            }
        };

        let res_id = self.symbol_table.new_identifier_id();
        let res_id_expr = utils::build_texpr_from_id(ty::Type::Boolean, res_id);

        let stmts = vec![
            ir::Statement::VarDecl {
                ty: ty::Type::Boolean,
                id: res_id,
                init: Some(init),
            },
            ir::Statement::If {
                condition: cond,
                body: vec![
                    ir::Statement::Expression(utils::build_assign(res_id_expr.clone(), rhs)),
                ],
                else_clause: vec![],
            },
        ];

        Ok(ir::TypedExpression {
            ty: ty::Type::Boolean,
            expr: ir::Expression::Block(Box::new(ir::BlockExpression {
                stmts,
                final_expr: utils::lvalue_to_rvalue(res_id_expr),
            })),
        })
    }

    fn translate_new_array(
        &mut self,
        base_ty: ty::Type,
        mut sizes: Vec<Spanned<ast::Expression>>,
    ) -> TranslationResult<ir::TypedExpression> {
        let mut array_ty = base_ty.clone();
        let mut sub_ty = None;
        for _ in 0..sizes.len() {
            sub_ty = Some(array_ty.clone());
            array_ty = ty::Type::Array(Box::new(array_ty));
        }
        let sub_ty = sub_ty.unwrap();

        let next_sizes = sizes.split_off(1);
        let current_size = sizes.into_iter().next().unwrap();

        let size_span = current_size.span;
        let current_size = self.translate_expression(current_size)?;
        let current_size = utils::lvalue_to_rvalue(current_size);
        utils::check_eq_types(&ty::Type::Int, &current_size.ty, size_span)?;

        let array = ir::TypedExpression {
            ty: array_ty.clone(),
            expr: ir::Expression::NewArray {
                sub_ty: sub_ty.clone(),
                size: Box::new(current_size.clone()),
            },
        };

        let default_value = if next_sizes.is_empty() {
            utils::default_value_for_ty(&sub_ty)
        } else {
            self.translate_new_array(base_ty, next_sizes)?
        };

        let (array_expr, block) = self.create_loop(sub_ty, array, |expr| {
            Ok(vec![
                ir::Statement::Expression(utils::build_assign(expr, default_value)),
            ])
        })?;

        Ok(ir::TypedExpression {
            ty: array_ty,
            expr: ir::Expression::Block(Box::new(ir::BlockExpression {
                stmts: block,
                final_expr: utils::lvalue_to_rvalue(array_expr),
            })),
        })
    }

    pub fn create_loop<F: FnOnce(ir::TypedExpression) -> TranslationResult<ir::BlockStatement>>(
        &mut self,
        ty: ty::Type,
        array: ir::TypedExpression,
        body_builder: F,
    ) -> TranslationResult<(ir::TypedExpression, ir::BlockStatement)> {
        // initialization of the counter and the array
        let index_id = self.symbol_table.new_identifier_id();
        let index_expr = utils::build_texpr_from_id(ty::Type::Int, index_id);
        let index_rvalue = utils::lvalue_to_rvalue(index_expr.clone());
        let array_id = self.symbol_table.new_identifier_id();
        let array_expr = utils::build_texpr_from_id(array.ty.clone(), array_id);
        let array_rvalue = utils::lvalue_to_rvalue(array_expr.clone());

        let const0 = utils::literal_to_texpr(common::Literal::IntLiteral(0));
        let array_len_expr = ir::TypedExpression {
            ty: ty::Type::Int,
            expr: ir::Expression::ArrayLength(Box::new(array_rvalue.clone())),
        };

        // translation of current loop value
        let array_indexed = ir::TypedExpression {
            ty: ty::Type::LValue(Box::new(ty)),
            expr: ir::Expression::Subscript {
                array: Box::new(array_rvalue.clone()),
                index: Box::new(index_rvalue.clone()),
            },
        };

        // translation of index++
        let index_inc = ir::TypedExpression {
            ty: ty::Type::LValue(Box::new(ty::Type::Int)),
            expr: ir::Expression::LValueUnaryOperator {
                lvalue_unop: ir::LValueUnaryOperatorKind::IntIncrement,
                sub: Box::new(index_expr.clone()),
            },
        };

        // body
        let mut body = body_builder(array_indexed)?;
        body.push(ir::Statement::Expression(index_inc));

        // finalization
        Ok((
            array_expr,
            vec![
                ir::Statement::VarDecl {
                    ty: array_rvalue.ty.clone(),
                    id: array_id,
                    init: Some(array),
                },
                ir::Statement::VarDecl {
                    ty: ty::Type::Int,
                    id: index_id,
                    init: Some(const0),
                },
                ir::Statement::While {
                    condition: ir::TypedExpression {
                        ty: ty::Type::Boolean,
                        expr: ir::Expression::BinaryOperator {
                            binop: ir::BinaryOperatorKind::IntLess,
                            lhs: Box::new(index_rvalue.clone()),
                            rhs: Box::new(array_len_expr),
                        },
                    },
                    body,
                },
            ],
        ))
    }
}
