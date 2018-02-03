use ty;
use ir;
use common;
use ir::IdentifierId;
use errors::TranslationError;
use ir_translator::TranslationResult;
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

pub fn build_texpr_from_id(ty: ty::Type, id: IdentifierId) -> TypedExpression {
    TypedExpression {
        ty: ty::Type::LValue(Box::new(ty)),
        expr: ir::Expression::Identifier(id),
    }
}

pub fn build_assign_to_id(id: IdentifierId, rhs: ir::Expression) -> ir::Expression {
    ir::Expression::Assign {
        lhs: Box::new(ir::Expression::Identifier(id)),
        rhs: Box::new(rhs),
    }
}

pub fn build_assign(lhs: TypedExpression, rhs: TypedExpression) -> TypedExpression {
    TypedExpression {
        ty: rhs.ty,
        expr: ir::Expression::Assign {
            lhs: Box::new(lhs.expr),
            rhs: Box::new(rhs.expr),
        },
    }
}

pub fn check_eq_types(a: &ty::Type, b: &ty::Type, error_span: Span) -> TranslationResult<()> {
    if a != b {
        error!(
            TranslationError::MismatchingTypes(a.clone(), b.clone(),),
            error_span
        )
    } else {
        Ok(())
    }
}

pub fn check_expect_type(
    expected: &ty::Type,
    given: &ty::Type,
    error_span: Span,
) -> TranslationResult<()> {
    if expected != given {
        error!(
            TranslationError::UnexpectedType(expected.clone(), given.clone(),),
            error_span
        )
    } else {
        Ok(())
    }
}

pub fn lvalue_to_rvalue(expression: TypedExpression) -> TypedExpression {
    match expression.ty {
        ty::Type::LValue(sub) => TypedExpression {
            ty: *sub,
            expr: ir::Expression::LValueToRValue(Box::new(expression.expr)),
        },
        other => TypedExpression {
            ty: other,
            expr: expression.expr,
        },
    }
}

pub fn unsure_subscriptable(expr: TypedExpression) -> Option<(ty::Type, ir::Expression)> {
    match expr.ty.clone() {
        ty::Type::Pointer(sub) => Some((*sub, expr.expr)),
        _ => None,
    }
}

pub fn default_value_for_ty(ty: &ty::Type) -> TypedExpression {
    let lit = match *ty {
        ty::Type::Int => common::Literal::IntLiteral(0),
        ty::Type::Double => common::Literal::DoubleLiteral(0.0),
        ty::Type::Boolean => common::Literal::BooleanLiteral(false),
        _ => panic!("This type doesn't have a default value"),
    };
    literal_to_texpr(lit)
}

pub fn literal_to_texpr(lit: common::Literal) -> TypedExpression {
    let ty = lit.get_type();
    TypedExpression {
        ty,
        expr: ir::Expression::Literal(lit),
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
