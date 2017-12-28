use ast;
use ty;
use ir;
use ir::symbol_table::{SymbolTable, GlobalsTable};

#[derive(Debug, Clone)]
pub enum TranslationError {
    FunctionAlreadyDefined(String),
    ParameterAlreadyDefined(String),
    LocalAlreadyDefined(String),
    MismatchingTypes(ty::Type, ty::Type),
    UndefinedLocal(String),
    NonLValueAssign,
    BinOpUndefined(ast::BinaryOperatorKind, ty::Type, ty::Type),
    LazyOpUndefined(ast::LazyOperatorKind, ty::Type, ty::Type),
    UnOpUndefined(ast::UnaryOperatorKind, ty::Type),
    FunctionCallArity(usize, usize),
    FunctionUndefined(String),
    IncDecNonLValue
}

pub type TranslationResult<T> = Result<T, TranslationError>;

pub fn translate_program(program: ast::Program) -> TranslationResult<ir::Program> {
    let mut globals_table = GlobalsTable::new();
    
    globals_table.register_function("printInt".to_string(), ty::FunctionType {
        return_ty: ty::Type::Void,
        parameters_ty: vec![ty::Type::Int]
    });
    globals_table.register_function("printDouble".to_string(), ty::FunctionType {
        return_ty: ty::Type::Void,
        parameters_ty: vec![ty::Type::Double]
    });
    globals_table.register_function("printString".to_string(), ty::FunctionType {
        return_ty: ty::Type::Void,
        parameters_ty: vec![ty::Type::String]
    });

    globals_table.register_function("readInt".to_string(), ty::FunctionType {
        return_ty: ty::Type::Int,
        parameters_ty: Vec::new()
    });
    globals_table.register_function("readDouble".to_string(), ty::FunctionType {
        return_ty: ty::Type::Double,
        parameters_ty: Vec::new()
    });


    for func in &program.declarations {
        if globals_table.register_function(func.name.clone(), func.get_type()) {
            return Err(TranslationError::FunctionAlreadyDefined(func.name.clone()))
        }
    }

    let mut declarations = Vec::with_capacity(program.declarations.len());
    for decl in program.declarations {
        declarations.push(translate_function(&globals_table, decl)?);
    }

    Ok(ir::Program {
        declarations
    })
}

fn translate_function(globals: &GlobalsTable, function: ast::Function) -> TranslationResult<ir::Function> {
    let mut symbol_table = SymbolTable::new(globals);
    symbol_table.begin_scope();

    for (param_ty, param_name) in function.parameters.clone() {
        if symbol_table.register_local(param_name.clone(), param_ty) {
            return Err(TranslationError::ParameterAlreadyDefined(param_name))
        }
    }

    symbol_table.begin_scope();

    let mut func_infos = FunctionInfos::new(function.return_ty);
    let body = translate_block_statement(&mut symbol_table, function.body, &mut func_infos)?;

    symbol_table.end_scope();
    symbol_table.end_scope();

    Ok(ir::Function {
        return_ty: function.return_ty,
        name: function.name,
        parameters: function.parameters,
        body
    })
}

fn translate_block_statement(st: &mut SymbolTable, block: ast::BlockStatement, fi: &mut FunctionInfos) -> TranslationResult<ir::BlockStatement> {
    st.begin_scope();
    
    let block = {
        let mut builder = BlockBuilder::new(st, fi);

        for stmt in block {
            builder.translate_statement(stmt)?;
        }

        builder.collect()
    };

    st.end_scope();
    Ok(block)
}

#[derive(Debug)]
struct FunctionInfos {
    temp_counter: usize,
    ret_ty: ty::Type,
}

impl FunctionInfos {
    fn new(ret_ty: ty::Type) -> Self {
        FunctionInfos {
            temp_counter: 0,
            ret_ty
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
            func_infos: fi
        }
    }

    fn collect(self) -> ir::BlockStatement {
        self.statements
    }

    fn translate_statement_as_block(&mut self, statement: ast::Statement) -> TranslationResult<ir::BlockStatement> {
        match statement {
            ast::Statement::Empty => Ok(ir::BlockStatement::new()),
            ast::Statement::Block(b) => translate_block_statement(self.symbol_table, b, self.func_infos),
            other => translate_block_statement(self.symbol_table, vec![other], self.func_infos)
        }
    }

    fn translate_statement(&mut self, statement: ast::Statement) -> TranslationResult<()> {
        match statement {
            ast::Statement::Empty => {},
            ast::Statement::Block(block) => {
                let block = translate_block_statement(self.symbol_table, block, self.func_infos)?;
                self.statements.push(ir::Statement::Block(block));
            },
            ast::Statement::VarDecl { ty, declarations } => {

                for (name, value) in declarations {
                    let value = if let Some(value) = value {
                        let ty_expr = self.translate_expression(value)?;
                        if ty_expr.qual_ty.ty != ty {
                            return Err(TranslationError::MismatchingTypes(ty_expr.qual_ty.ty, ty));
                        }
                        ty_expr
                    } else {
                        ir::TypedExpression {
                            qual_ty: ty::QualifiedType::new(ty, false),
                            expr: ir::Expression::DefaultValue
                        }
                    };
                    
                    if self.symbol_table.register_local(name.clone(), ty) {
                        return Err(TranslationError::LocalAlreadyDefined(name.clone()))
                    }
                    
                    self.statements.push(ir::Statement::VarDecl {
                        ty,
                        name,
                        value
                    });
                }
            },
            ast::Statement::If { condition, body, else_clause } => {
                let condition = self.translate_expression(condition)?;
                if condition.qual_ty.ty != ty::Type::Boolean {
                    return Err(TranslationError::MismatchingTypes(ty::Type::Boolean, condition.qual_ty.ty))
                }

                let body = self.translate_statement_as_block(*body)?;

                let else_clause = if let Some(stmt) = else_clause {
                    self.translate_statement_as_block(*stmt)?
                } else {
                    ir::BlockStatement::new()
                };

                self.statements.push(ir::Statement::If {
                    condition,
                    body,
                    else_clause
                })
            },
            ast::Statement::While { condition, body } => {
                let condition = self.translate_expression(condition)?;
                if condition.qual_ty.ty != ty::Type::Boolean {
                    return Err(TranslationError::MismatchingTypes(ty::Type::Boolean, condition.qual_ty.ty))
                }

                let body = self.translate_statement_as_block(*body)?;

                self.statements.push(ir::Statement::While {
                    condition,
                    body,
                })
            },
            ast::Statement::Return(maybe_expr) => {
                let expr = if let Some(expr) = maybe_expr {
                    let expr = self.translate_expression(expr)?;

                    if expr.qual_ty.ty != self.func_infos.ret_ty {
                        return Err(TranslationError::MismatchingTypes(expr.qual_ty.ty, self.func_infos.ret_ty))
                    }

                    expr
                } else {
                    if ty::Type::Void != self.func_infos.ret_ty {
                        return Err(TranslationError::MismatchingTypes(ir::Type::Void, self.func_infos.ret_ty))
                    }
                    ir::TypedExpression {
                        qual_ty: ty::QualifiedType::new(ty::Type::Void, false),
                        expr: ir::Expression::DefaultValue
                    }
                };

                self.statements.push(ir::Statement::Return(expr));
            },
            ast::Statement::Expression(expr) => {
                let expr = self.translate_expression(expr)?;
                self.statements.push(ir::Statement::Expression(expr));
            },
            ast::Statement::Break => {
                // TODO check in loop
                self.statements.push(ir::Statement::Break);
            },
            ast::Statement::Continue => {
                // TODO check in loop
                self.statements.push(ir::Statement::Continue);
            }
        }
        Ok(())
    }

    fn translate_expression(&mut self, expression: ast::Expression) -> TranslationResult<ir::TypedExpression> {
            
        match expression {
            ast::Expression::Literal(lit) => {
                let (ty, lit) = match lit {
                    ast::Literal::IntLiteral(i)
                        => (ty::Type::Int, ir::Literal::IntLiteral(i)),
                    ast::Literal::DoubleLiteral(d)
                        => (ty::Type::Double, ir::Literal::DoubleLiteral(d)),
                    ast::Literal::BooleanLiteral(b)
                        => (ty::Type::Boolean, ir::Literal::BooleanLiteral(b)),
                    ast::Literal::StringLiteral(s)
                        => (ty::Type::String, ir::Literal::StringLiteral(s))
                };

                Ok(ir::TypedExpression {
                    qual_ty: ty::QualifiedType::new(ty, false),
                    expr: ir::Expression::Literal(lit)
                })
            },
            ast::Expression::Identifier(id) => {
                if let Some(&ty) = self.symbol_table.lookup_local(&id) {
                    let qual_ty = ty::QualifiedType::new(ty, true);
                    Ok(ir::TypedExpression {
                        qual_ty,
                        expr: ir::Expression::Identifier(id)
                    })
                } else {
                    Err(TranslationError::UndefinedLocal(id))
                }
            },
            ast::Expression::Assign { lhs, rhs } => {
                let lhs = self.translate_expression(*lhs)?;
                let rhs = self.translate_expression(*rhs)?;

                if lhs.qual_ty.ty != rhs.qual_ty.ty {
                    return Err(TranslationError::MismatchingTypes(lhs.qual_ty.ty, rhs.qual_ty.ty));
                }

                if !lhs.qual_ty.lvalue {
                    return Err(TranslationError::NonLValueAssign);
                }

                let qual_ty = rhs.qual_ty;
                let expr = ir::Expression::Assign {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };

                Ok(ir::TypedExpression {
                    qual_ty,
                    expr
                })
            },
            ast::Expression::BinaryOperator { binop, lhs, rhs } => {
                let lhs = self.translate_expression(*lhs)?;
                let rhs = self.translate_expression(*rhs)?;

                if let Some((ty, op)) = binop_typeck(binop, lhs.qual_ty.ty, rhs.qual_ty.ty) {
                    let expr = ir::Expression::BinaryOperator {
                        binop: op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    };
                    Ok(ir::TypedExpression {
                        qual_ty: ty::QualifiedType::new(ty, false),
                        expr,
                    })
                } else {
                    Err(TranslationError::BinOpUndefined(binop, lhs.qual_ty.ty, rhs.qual_ty.ty))
                }
            },
            ast::Expression::LazyOperator { lazyop, lhs, rhs } => {
                let lhs = self.translate_expression(*lhs)?;
                let rhs = self.translate_expression(*rhs)?;

                if let Some((ty, op)) = lazyop_typeck(lazyop, lhs.qual_ty.ty, rhs.qual_ty.ty) {
                    let expr = ir::Expression::LazyOperator {
                        lazyop: op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    };
                    Ok(ir::TypedExpression {
                        qual_ty: ty::QualifiedType::new(ty, false),
                        expr,
                    })
                } else {
                    Err(TranslationError::LazyOpUndefined(lazyop, lhs.qual_ty.ty, rhs.qual_ty.ty))
                }
            },
            ast::Expression::UnaryOperator { unop, sub } => {
                let sub = self.translate_expression(*sub)?;

                if let Some((ty, op)) = unop_typeck(unop, sub.qual_ty.ty) {
                    let expr = ir::Expression::UnaryOperator {
                        unop: op,
                        sub: Box::new(sub),
                    };
                    Ok(ir::TypedExpression {
                        qual_ty: ty::QualifiedType::new(ty, false),
                        expr
                    })
                } else {
                    Err(TranslationError::UnOpUndefined(unop, sub.qual_ty.ty))
                }
            },
            ast::Expression::Increment(sub) => {
                let sub = self.translate_expression(*sub)?;
                if sub.qual_ty.ty != ty::Type::Int {
                    return Err(TranslationError::MismatchingTypes(ty::Type::Int, sub.qual_ty.ty))
                }

                if !sub.qual_ty.lvalue {
                    return Err(TranslationError::IncDecNonLValue)
                }

                let qual_ty = sub.qual_ty;

                Ok(ir::TypedExpression {
                    qual_ty,
                    expr: ir::Expression::Increment(Box::new(sub))
                })
            },
            ast::Expression::Decrement(sub) => {
                let sub = self.translate_expression(*sub)?;
                if sub.qual_ty.ty != ty::Type::Int {
                    return Err(TranslationError::MismatchingTypes(ty::Type::Int, sub.qual_ty.ty))
                }

                if !sub.qual_ty.lvalue {
                    return Err(TranslationError::IncDecNonLValue)
                }

                let qual_ty = sub.qual_ty;

                Ok(ir::TypedExpression {
                    qual_ty,
                    expr: ir::Expression::Decrement(Box::new(sub))
                })
            },
            ast::Expression::FunctionCall { function, args } => {
                if let Some(func_ty) = self.symbol_table.lookup_function(&function).cloned() {

                    let mut args_translated = Vec::with_capacity(args.len());
                    if func_ty.parameters_ty.len() != args.len() {
                        return Err(TranslationError::FunctionCallArity(func_ty.parameters_ty.len(), args_translated.len()))
                    }

                    for (arg, &param_ty) in args.into_iter().zip(func_ty.parameters_ty.iter()) {
                        let arg = self.translate_expression(arg)?;
                        if arg.qual_ty.ty != param_ty {
                            return Err(TranslationError::MismatchingTypes(arg.qual_ty.ty, param_ty))
                        }
                        args_translated.push(arg);
                    }
                    let ret_ty = func_ty.return_ty;
                    Ok(ir::TypedExpression {
                        qual_ty: ty::QualifiedType::new(ret_ty, false),
                        expr: ir::Expression::FunctionCall {
                            function,
                            args: args_translated
                        }
                    })
                } else {
                    Err(TranslationError::FunctionUndefined(function))
                }
            }
        }
    }
}


fn binop_typeck(binop: ast::BinaryOperatorKind, lhs: ty::Type, rhs: ty::Type) -> Option<(ty::Type, ir::BinaryOperatorKind)> {
    use ast::BinaryOperatorKind::*;
    match (binop, lhs, rhs) {
        (Plus, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Int, ir::BinaryOperatorKind::IntPlus)),
        (Plus, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Double, ir::BinaryOperatorKind::DoublePlus)),
        (Minus, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Int, ir::BinaryOperatorKind::IntMinus)),
        (Minus, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Double, ir::BinaryOperatorKind::DoubleMinus)),
        (Multiply, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Int, ir::BinaryOperatorKind::IntMultiply)),
        (Multiply, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Double, ir::BinaryOperatorKind::DoubleMultiply)),
        (Divide, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Int, ir::BinaryOperatorKind::IntDivide)),
        (Divide, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Double, ir::BinaryOperatorKind::DoubleDivide)),
        (Modulo, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Int, ir::BinaryOperatorKind::IntModulo)),
        
        (Equal, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntEqual)),
        (Equal, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleEqual)),
        (Equal, ty::Type::Boolean, ty::Type::Boolean) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::BooleanEqual)),

        (NotEqual, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntNotEqual)),
        (NotEqual, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleNotEqual)),
        (NotEqual, ty::Type::Boolean, ty::Type::Boolean) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::BooleanNotEqual)),

        (Less, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntLess)),
        (Less, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleLess)),
    
        (LessEqual, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntLessEqual)),
        (LessEqual, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleLessEqual)),

        (Greater, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntGreater)),
        (Greater, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleGreater)),

        (GreaterEqual, ty::Type::Int, ty::Type::Int) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntGreaterEqual)),
        (GreaterEqual, ty::Type::Double, ty::Type::Double) => Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleGreaterEqual)),

        _ => None
    }
}

fn lazyop_typeck(lazyop: ast::LazyOperatorKind, lhs: ty::Type, rhs: ty::Type) -> Option<(ty::Type, ir::LazyOperatorKind)> {
    use ast::LazyOperatorKind::*;

    match (lazyop, lhs, rhs) {
        (LogicalAnd, ty::Type::Boolean, ty::Type::Boolean) => Some((ty::Type::Boolean, ir::LazyOperatorKind::BooleanLogicalAnd)),
        (LogicalOr, ty::Type::Boolean, ty::Type::Boolean) => Some((ty::Type::Boolean, ir::LazyOperatorKind::BooleanLogicalOr)),
        _ => None
    }
}

fn unop_typeck(unop: ast::UnaryOperatorKind, sub: ty::Type) -> Option<(ty::Type, ir::UnaryOperatorKind)> {
    use ast::UnaryOperatorKind::*;

    match (unop, sub) {
        (Minus, ty::Type::Int) => Some((ty::Type::Int, ir::UnaryOperatorKind::IntMinus)),
        (Minus, ty::Type::Double) => Some((ty::Type::Double, ir::UnaryOperatorKind::DoubleMinus)),
        (LogicalNot, ty::Type::Boolean) => Some((ty::Type::Boolean, ir::UnaryOperatorKind::BooleanNot)),
        _ => None
    }
}
