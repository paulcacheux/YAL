use ast;
use ty;
use ir;
use common;
use codemap::*;
use errors::TranslationError;

pub mod tables;
#[macro_use]
mod utils;
mod typeck;
mod func_trans;
mod pretrans;

use self::func_trans::*;
use self::tables::{Tables, TypeTable};

pub type TranslationResult<T> = Result<T, Spanned<TranslationError>>;

pub fn translate_program(
    tables: &mut Tables,
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
    pretrans::translate_types(tables, structs)?;

    // translate extern functions and collect names
    for exfunc in exfunctions {
        let func_ty = exfunc.get_type();
        let func_ty = translate_function_type(&mut tables.types, func_ty)?;
        if tables
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
        let func_ty = translate_function_type(&mut tables.types, func_ty)?;
        if tables.globals.register_function(func.name.clone(), func_ty) {
            return error!(
                TranslationError::FunctionAlreadyDefined(func.name.clone()),
                func.span
            );
        }
    }

    // translate local functions
    for func in functions {
        declarations.push(ir::Declaration::Function(translate_function(tables, func)?))
    }

    Ok(ir::Program { declarations })
}

fn translate_function(
    tables: &mut Tables,
    function: ast::Function,
) -> TranslationResult<ir::Function> {
    tables.new_locals();
    tables.locals.begin_scope();

    let mut parameters = Vec::with_capacity(function.parameters.len());
    for (param_name, param_ty) in function.parameters {
        let param_ty = translate_type(&mut tables.types, param_ty, false)?;
        if let Some(id) = tables.locals.register_local(param_name.clone(), param_ty) {
            parameters.push((param_ty, id));
        } else {
            return error!(
                TranslationError::ParameterAlreadyDefined(param_name),
                function.span
            );
        }
    }

    tables.locals.begin_scope();

    let func_return_ty = translate_type(&mut tables.types, function.return_ty, true)?;

    let (mut body, var_declarations) = {
        let mut func_builder = FunctionBuilder::new(tables, func_return_ty);
        let mut body = func_builder.translate_block_statement(function.body)?;
        (body, func_builder.var_declarations)
    };

    if !utils::check_return_paths(&body) {
        if func_return_ty != tables.types.get_void_ty() {
            return error!(TranslationError::NotAllPathsReturn, function.span);
        } else {
            body.push(ir::Statement::Return(None)); // we add a return void
        }
    }

    tables.locals.end_scope();
    tables.locals.end_scope();

    Ok(ir::Function {
        return_ty: func_return_ty,
        name: function.name,
        parameters,
        var_declarations,
        body,
        span: function.span,
    })
}

pub fn check_if_main_declaration(tables: &Tables, prog: &ir::Program) -> TranslationResult<()> {
    for decl in &prog.declarations {
        let (name, ty, span) = match *decl {
            ir::Declaration::ExternFunction(ref exfunc) => {
                (&exfunc.name, exfunc.ty.clone(), exfunc.span)
            }
            ir::Declaration::Function(ref func) => (&func.name, func.get_type(), func.span),
        };

        if name == "main" {
            if ty.return_ty == tables.types.get_int_ty() && ty.parameters_ty.is_empty()
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
    typectxt: &mut TypeTable,
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
        ast::Type::Array(sub_ty, size) => {
            let sub = translate_type(typectxt, *sub_ty, false)?;
            Ok(typectxt.array_of(sub, size))
        }
        _ => unimplemented!(),
    }
}

fn translate_function_type(
    typectxt: &mut TypeTable,
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
