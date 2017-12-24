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
    FunctionUndefined(String)
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

fn translate_expression_as_block(st: &mut SymbolTable, expression: ast::Expression, fi: &mut FunctionInfos) -> TranslationResult<(ir::BlockStatement, VarNameTyped)> {
    st.begin_scope();
    
    let res = {
        let mut builder = BlockBuilder::new(st, fi);
        
        let vnt = builder.translate_expression(expression)?;
        let block = builder.collect();
        (block, vnt)
    };

    st.end_scope();
    Ok(res)
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

    fn gensym(&mut self) -> ir::VarName {
        let t = self.temp_counter;
        self.temp_counter += 1;
        ir::VarName::Temp(t)
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

    fn translate_statement(&mut self, statement: ast::Statement) -> TranslationResult<()> {
        match statement {
            ast::Statement::Empty => {},
            ast::Statement::Block(block) => {
                let block = translate_block_statement(self.symbol_table, block, self.func_infos)?;
                self.statements.push(ir::Statement::Block(block));
            },
            ast::Statement::VarDecl { ty, declarations } => {
                let def_value = match ty {
                    ty::Type::Int => ir::Expression::Literal(ir::Literal::IntLiteral(0)),
                    ty::Type::Double => ir::Expression::Literal(ir::Literal::DoubleLiteral(0.0)),
                    ty::Type::Boolean => ir::Expression::Literal(ir::Literal::BooleanLiteral(false)),
                    _ => panic!("Unexpected type in vardecl")
                };

                for (name, value) in declarations {
                    let value = if let Some(value) = value {
                        let value_name = self.translate_expression(value)?;
                        if value_name.qual_ty.ty != ty {
                            return Err(TranslationError::MismatchingTypes(value_name.qual_ty.ty, ty));
                        }
                        ir::Expression::Var(value_name.varname)
                    } else {
                        def_value.clone()
                    };
                    
                    if self.symbol_table.register_local(name.clone(), ty) {
                        return Err(TranslationError::LocalAlreadyDefined(name.clone()))
                    }
                    
                    let var_name = ir::VarName::Id(name.clone());
                    self.statements.push(ir::Statement::VarDecl {
                        ty,
                        name: var_name.clone(),
                        value
                    });
                }
            },
            ast::Statement::If { condition, body, else_clause } => {
                let vnt_condition = self.translate_expression(condition)?;
                if vnt_condition.qual_ty.ty != ty::Type::Boolean {
                    return Err(TranslationError::MismatchingTypes(ty::Type::Boolean, vnt_condition.qual_ty.ty))
                }

                let body = match *body {
                    ast::Statement::Block(b)
                        => translate_block_statement(self.symbol_table, b, self.func_infos)?,
                    other
                        => translate_block_statement(self.symbol_table, vec![other], self.func_infos)?
                };

                let else_clause = match else_clause.map(|e| *e) {
                    Some(ast::Statement::Block(b))
                        => translate_block_statement(self.symbol_table, b, self.func_infos)?,
                    Some(other)
                        => translate_block_statement(self.symbol_table, vec![other], self.func_infos)?,
                    None => ir::BlockStatement::new()
                };

                self.statements.push(ir::Statement::If {
                    condition: vnt_condition.varname,
                    body,
                    else_clause
                })
            },
            ast::Statement::While { condition, body } => {
                let fake_stmt = vec![
                    ast::Statement::If {
                        condition,
                        body,
                        else_clause: Some(Box::new(ast::Statement::Break))
                    }
                ];
                let block = translate_block_statement(self.symbol_table, fake_stmt, self.func_infos)?;
                self.statements.push(ir::Statement::Loop {
                    body: block
                });
            },
            ast::Statement::Return(maybe_expr) => {
                let (inner, ty) = if let Some(expr) = maybe_expr {
                    let vnt = self.translate_expression(expr)?;
                    
                    (Some(vnt.varname), vnt.qual_ty.ty)
                } else {
                    (None, ty::Type::Void)
                };

                if ty != self.func_infos.ret_ty {
                    return Err(TranslationError::MismatchingTypes(ty, self.func_infos.ret_ty))
                }

                self.statements.push(ir::Statement::Return(inner))
            },
            ast::Statement::Expression(expr) => {
                self.translate_expression(expr)?;
            },
            ast::Statement::Break => {
                self.statements.push(ir::Statement::Break);
            },
            ast::Statement::Continue => {
                self.statements.push(ir::Statement::Continue);
            }
        }
        Ok(())
    }

    fn translate_temp_assign(&mut self, ty: ty::Type, expr: ir::Expression) -> VarNameTyped {
        let vn = self.func_infos.gensym();
        self.statements.push(ir::Statement::VarDecl {
            ty,
            name: vn.clone(),
            value: expr
        });
        VarNameTyped {
            varname: vn,
            qual_ty: ty::QualifiedType::new(ty, false)
        }
    }

    

    fn translate_expression(&mut self, expression: ast::Expression) -> TranslationResult<VarNameTyped> {
        
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
                Ok(self.translate_temp_assign(ty, ir::Expression::Literal(lit)))
            },
            ast::Expression::Identifier(id) => {
                if let Some(&ty) = self.symbol_table.lookup_local(&id) {
                    let vn = ir::VarName::Id(id);
                    let qual_ty = ty::QualifiedType::new(ty, true);
                    Ok(VarNameTyped {
                        varname: vn,
                        qual_ty
                    })
                } else {
                    Err(TranslationError::UndefinedLocal(id))
                }
            },
            ast::Expression::Assign { lhs, rhs } => {
                let lhs_vnt = self.translate_expression(*lhs)?;
                let rhs_vnt = self.translate_expression(*rhs)?;

                if lhs_vnt.qual_ty.ty != rhs_vnt.qual_ty.ty {
                    return Err(TranslationError::MismatchingTypes(lhs_vnt.qual_ty.ty, rhs_vnt.qual_ty.ty));
                }

                if !lhs_vnt.qual_ty.lvalue {
                    return Err(TranslationError::NonLValueAssign);
                }

                self.statements.push(ir::Statement::Assign {
                    name: lhs_vnt.varname,
                    value: ir::Expression::Var(rhs_vnt.varname.clone())
                });
                Ok(rhs_vnt)
            },
            ast::Expression::BinaryOperator { binop, lhs, rhs } => {
                let lhs_vnt = self.translate_expression(*lhs)?;
                let rhs_vnt = self.translate_expression(*rhs)?;

                if let Some((ty, op)) = binop_typeck(binop, lhs_vnt.qual_ty.ty, rhs_vnt.qual_ty.ty) {
                    let expr = ir::Expression::BinaryOperator {
                        binop: op,
                        lhs: lhs_vnt.varname,
                        rhs: rhs_vnt.varname
                    };
                    Ok(self.translate_temp_assign(ty, expr))
                } else {
                    Err(TranslationError::BinOpUndefined(binop, lhs_vnt.qual_ty.ty, rhs_vnt.qual_ty.ty))
                }
            },
            ast::Expression::LazyOperator { lazyop, lhs, rhs } => {
                let lhs_vnt = self.translate_expression(*lhs)?;

                if lhs_vnt.qual_ty.ty != ty::Type::Boolean {
                    return Err(TranslationError::LazyOpUndefined(lazyop, lhs_vnt.qual_ty.ty, ty::Type::Boolean))
                }

                let res_vnt = self.translate_temp_assign(ty::Type::Boolean, ir::Expression::Var(lhs_vnt.varname));

                let (mut final_block, rhs_vnt) = translate_expression_as_block(self.symbol_table, *rhs, self.func_infos)?;
                final_block.push(ir::Statement::Assign {
                    name: res_vnt.varname.clone(),
                    value: ir::Expression::Var(rhs_vnt.varname)
                });

                if rhs_vnt.qual_ty.ty != ty::Type::Boolean {
                    return Err(TranslationError::LazyOpUndefined(lazyop, rhs_vnt.qual_ty.ty, ty::Type::Boolean))
                }
                
                match lazyop {
                    ast::LazyOperatorKind::LogicalAnd => {
                        let if_stmt = ir::Statement::If {
                            condition: res_vnt.varname.clone(),
                            body: final_block,
                            else_clause: Vec::new(),
                        };
                        self.statements.push(if_stmt);
                    },
                    ast::LazyOperatorKind::LogicalOr => {
                        let if_stmt = ir::Statement::If {
                            condition: res_vnt.varname.clone(),
                            body: Vec::new(),
                            else_clause: final_block
                        };
                        self.statements.push(if_stmt);
                    }
                }

                Ok(res_vnt)
            },
            ast::Expression::UnaryOperator { unop, sub } => {
                let sub_vnt = self.translate_expression(*sub)?;

                if let Some((ty, op)) = unop_typeck(unop, sub_vnt.qual_ty.ty) {
                    let expr = ir::Expression::UnaryOperator {
                        unop: op,
                        sub: sub_vnt.varname,
                    };
                    Ok(self.translate_temp_assign(ty, expr))
                } else {
                    Err(TranslationError::UnOpUndefined(unop, sub_vnt.qual_ty.ty))
                }
            },
            ast::Expression::Increment(sub) => {
                let sub_vnt = self.translate_expression(*sub)?;
                if sub_vnt.qual_ty.ty != ty::Type::Int {
                    return Err(TranslationError::MismatchingTypes(ty::Type::Int, sub_vnt.qual_ty.ty))
                }

                self.statements.push(ir::Statement::Increment(sub_vnt.varname.clone()));
                Ok(sub_vnt)
            },
            ast::Expression::Decrement(sub) => {
                let sub_vnt = self.translate_expression(*sub)?;
                if sub_vnt.qual_ty.ty != ty::Type::Int {
                    return Err(TranslationError::MismatchingTypes(ty::Type::Int, sub_vnt.qual_ty.ty))
                }

                self.statements.push(ir::Statement::Decrement(sub_vnt.varname.clone()));
                Ok(sub_vnt)
            },
            ast::Expression::FunctionCall { function, args } => {
                let mut args_vnt = Vec::with_capacity(args.len());
                for arg in args {
                    args_vnt.push(self.translate_expression(arg)?);
                }

                let mut args = Vec::with_capacity(args_vnt.len());
                let ret_ty = if let Some(func_ty) = self.symbol_table.lookup_function(&function) {
                    if func_ty.parameters_ty.len() != args_vnt.len() {
                        return Err(TranslationError::FunctionCallArity(func_ty.parameters_ty.len(), args_vnt.len()))
                    }

                    for (arg_vnt, &param_ty) in args_vnt.into_iter().zip(func_ty.parameters_ty.iter()) {
                        if arg_vnt.qual_ty.ty != param_ty {
                            return Err(TranslationError::MismatchingTypes(arg_vnt.qual_ty.ty, param_ty))
                        }
                        args.push(arg_vnt.varname);
                    }
                    func_ty.return_ty
                } else {
                    return Err(TranslationError::FunctionUndefined(function))
                };

                let expr = ir::Expression::FunctionCall {
                    function,
                    args
                };
                
                Ok(self.translate_temp_assign(ret_ty, expr))
            }
        }   
    }
}

#[derive(Debug, Clone)]
struct VarNameTyped {
    varname: ir::VarName,
    qual_ty: ty::QualifiedType,
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

fn unop_typeck(unop: ast::UnaryOperatorKind, sub: ty::Type) -> Option<(ty::Type, ir::UnaryOperatorKind)> {
    use ast::UnaryOperatorKind::*;

    match (unop, sub) {
        (Minus, ty::Type::Int) => Some((ty::Type::Int, ir::UnaryOperatorKind::IntMinus)),
        (Minus, ty::Type::Double) => Some((ty::Type::Double, ir::UnaryOperatorKind::DoubleMinus)),
        (LogicalNot, ty::Type::Boolean) => Some((ty::Type::Boolean, ir::UnaryOperatorKind::BooleanNot)),
        _ => None
    }
}
