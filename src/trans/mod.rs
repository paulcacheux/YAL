use ast;
use ty;
use ir;
use common;
use codemap::*;
use errors::TranslationError;

pub mod context;
pub mod symbol_table;
#[macro_use]
mod utils;
mod typeck;
mod block_trans;
mod pretrans;

use self::block_trans::*;
use self::context::Context;

pub type TranslationResult<T> = Result<T, Spanned<TranslationError>>;

pub fn translate_program(
    context: &mut Context,
    program: ast::Program,
    runtime: Option<ir::Program>,
) -> TranslationResult<ir::Program> {
    let mut declarations = runtime.map(|r| r.declarations).unwrap_or_default();
    declarations.reserve(program.declarations.len());

    let mut functions = Vec::new();
    let mut exfunctions = Vec::new();
    let mut structs = Vec::new();

    for decl in program.declarations {
        match decl {
            ast::Declaration::Struct(s) => structs.push(s),
            ast::Declaration::ExternFunction(exfunc) => exfunctions.push(exfunc),
            ast::Declaration::Function(func) => functions.push(func),
        }
    }

    // type building TODO check for cycles
    pretrans::translate_types(context, structs)?;

    // translate extern functions and collect names
    for exfunc in exfunctions {
        let func_ty = exfunc.get_type();
        let func_ty = translate_function_type(&mut context.types, func_ty)?;
        if context
            .globals
            .register_function(exfunc.name.clone(), func_ty.clone())
        {
            return error!(
                TranslationError::FunctionAlreadyDefined(exfunc.name.clone()),
                exfunc.span
            );
        }

        declarations.push(ir::Declaration::ExternFunction(ir::ExternFunction {
            ty: func_ty,
            name: exfunc.name,
            span: exfunc.span,
        }));
    }

    // collect names for local functions
    for func in &functions {
        let func_ty = func.get_type();
        let func_ty = translate_function_type(&mut context.types, func_ty)?;
        if context
            .globals
            .register_function(func.name.clone(), func_ty)
        {
            return error!(
                TranslationError::FunctionAlreadyDefined(func.name.clone()),
                func.span
            );
        }
    }

    // translate local functions
    for func in functions {
        declarations.push(ir::Declaration::Function(translate_function(
            context,
            func,
        )?))
    }

    Ok(ir::Program { declarations })
}

fn translate_function(
    context: &mut Context,
    function: ast::Function,
) -> TranslationResult<ir::Function> {
    context.new_locals();
    context.locals.begin_scope();

    let mut parameters = Vec::with_capacity(function.parameters.len());
    for (param_ty, param_name) in function.parameters {
        let param_ty = translate_type(&mut context.types, param_ty, false)?;
        if let Some(id) = context.locals.register_local(param_name.clone(), param_ty) {
            parameters.push((param_ty, id));
        } else {
            return error!(
                TranslationError::ParameterAlreadyDefined(param_name),
                function.span
            );
        }
    }

    context.locals.begin_scope();

    let func_return_ty = translate_type(&mut context.types, function.return_ty, true)?;
    let mut func_builder = FunctionBuilder::new(func_return_ty);
    let mut body = func_builder.translate_block_statement(context, function.body)?;

    if !utils::check_return_paths(&body) {
        if func_return_ty != context.types.get_void_ty() {
            return error!(TranslationError::NotAllPathsReturn, function.span);
        } else {
            body.push(ir::Statement::Return(None)); // we add a return void
        }
    }

    context.locals.end_scope();
    context.locals.end_scope();

    Ok(ir::Function {
        return_ty: func_return_ty,
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
        ctxt: &mut Context,
        block: ast::BlockStatement,
    ) -> TranslationResult<ir::BlockStatement> {
        ctxt.locals.begin_scope();

        let block = {
            let mut builder = BlockBuilder::new(ctxt, self);

            for stmt in block.statements {
                builder.translate_statement(stmt)?;
            }

            builder.collect()
        };

        ctxt.locals.end_scope();
        Ok(block)
    }
}

pub fn check_if_main_declaration(context: &Context, prog: &ir::Program) -> TranslationResult<()> {
    for decl in &prog.declarations {
        let (name, ty, span) = match *decl {
            ir::Declaration::ExternFunction(ref exfunc) => {
                (&exfunc.name, exfunc.ty.clone(), exfunc.span)
            }
            ir::Declaration::Function(ref func) => (&func.name, func.get_type(), func.span),
        };

        if name == "main" {
            if ty.return_ty == context.types.get_int_ty() && ty.parameters_ty.is_empty()
                && !ty.is_vararg
            {
                return Ok(());
            } else {
                return error!(TranslationError::MainWrongType, span);
            }
        }
    }
    error!(TranslationError::NoMain, Span::dummy())
}

fn translate_type(
    typectxt: &mut ty::TyContext,
    ty: Spanned<ast::Type>,
    void: bool,
) -> TranslationResult<ty::Type> {
    match ty.inner {
        ast::Type::Identifier(id) => {
            let ty_span = ty.span;
            if let Some(ty) = typectxt.lookup_type(&id) {
                if !void && ty == typectxt.get_void_ty() {
                    error!(TranslationError::UnexpectedVoid, ty_span)
                } else {
                    Ok(ty)
                }
            } else {
                error!(TranslationError::UndefinedType(id), ty_span)
            }
        }
        ast::Type::Pointer(sub_ty) => {
            let sub = translate_type(typectxt, *sub_ty, true)?;
            Ok(typectxt.pointer_of(sub))
        }
    }
}

fn translate_function_type(
    typectxt: &mut ty::TyContext,
    func_ty: ast::FunctionType,
) -> TranslationResult<ty::FunctionType> {
    let return_ty = translate_type(typectxt, func_ty.return_ty, true)?;
    let parameters_ty = func_ty
        .parameters_ty
        .into_iter()
        .map(|ty| translate_type(typectxt, ty, false))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ty::FunctionType {
        return_ty,
        parameters_ty,
        is_vararg: func_ty.is_vararg,
    })
}
