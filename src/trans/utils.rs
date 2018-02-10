use ty;
use ir;
use common;
use ir::IdentifierId;
use errors::TranslationError;
use trans::TranslationResult;
use codemap::{Span, Spanned};

macro_rules! error {
    ($err:expr, $span:expr) => {
        Err(Spanned::new($err, $span))
    }
}

#[derive(Debug, Clone)]
pub struct TypedExpression {
    pub ty: ty::Type,
    pub expr: ir::Expression,
}

pub fn build_assign_to_id(id: IdentifierId, rhs: ir::Expression) -> ir::Expression {
    ir::Expression::Assign {
        lhs: Box::new(ir::Expression::Identifier(id)),
        rhs: Box::new(rhs),
    }
}

pub fn check_eq_types(a: ty::Type, b: ty::Type, error_span: Span) -> TranslationResult<()> {
    if a != b {
        error!(TranslationError::MismatchingTypes(a, b), error_span) // TODO convert Type to suitable format
    } else {
        Ok(())
    }
}

pub fn check_expect_type(
    expected: ty::Type,
    given: ty::Type,
    error_span: Span,
) -> TranslationResult<()> {
    if expected != given {
        error!(
            TranslationError::UnexpectedType(expected, given),
            error_span
        )
    } else {
        Ok(())
    }
}

pub fn lvalue_to_rvalue(tyctxt: &ty::TyContext, expression: TypedExpression) -> TypedExpression {
    if let Some(sub) = tyctxt.is_lvalue(expression.ty) {
        TypedExpression {
            ty: sub,
            expr: ir::Expression::LValueToRValue(Box::new(expression.expr)),
        }
    } else {
        expression
    }
}

pub fn rvalue_to_lvalue(
    tyctxt: &mut ty::TyContext,
    expression: TypedExpression,
) -> TypedExpression {
    if tyctxt.is_lvalue(expression.ty).is_some() {
        expression
    } else {
        TypedExpression {
            ty: tyctxt.lvalue_of(expression.ty),
            expr: ir::Expression::RValueToLValue(Box::new(expression.expr)),
        }
    }
}

pub fn unsure_workable(tyctxt: &mut ty::TyContext, expr: TypedExpression) -> TypedExpression {
    if tyctxt.is_lvalue_struct(expr.ty).is_some() {
        expr
    } else if tyctxt.is_struct(expr.ty).is_some() {
        rvalue_to_lvalue(tyctxt, expr)
    } else {
        lvalue_to_rvalue(tyctxt, expr)
    }
}

pub fn unsure_subscriptable(
    tyctxt: &ty::TyContext,
    expr: TypedExpression,
) -> Option<(ty::Type, ir::Expression)> {
    if let Some(sub) = tyctxt.is_pointer(expr.ty) {
        Some((sub, expr.expr))
    } else {
        None
    }
}

pub fn check_return_paths(block: &[ir::Statement]) -> bool {
    block.iter().map(check_return_paths_stmt).any(|b| b)
}

pub fn check_return_paths_stmt(stmt: &ir::Statement) -> bool {
    match *stmt {
        ir::Statement::Block(ref b) => check_return_paths(b),
        ir::Statement::If {
            ref condition,
            ref body,
            ref else_clause,
        } => match *condition {
            ir::Expression::Literal(common::Literal::BooleanLiteral(true)) => {
                check_return_paths(body)
            }
            ir::Expression::Literal(common::Literal::BooleanLiteral(false)) => {
                check_return_paths(else_clause)
            }
            _ => check_return_paths(body) && check_return_paths(else_clause),
        },
        ir::Statement::While { ref condition, .. } => {
            if let ir::Expression::Literal(common::Literal::BooleanLiteral(true)) = *condition {
                true
            } else {
                false
            }
        }
        ir::Statement::Return(_) => true,
        _ => false,
    }
}
