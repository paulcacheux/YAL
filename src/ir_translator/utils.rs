use ty;
use ir;
use ir::IdentifierId;
use errors::TranslationError;
use ir_translator::TranslationResult;
use span::{Span, Spanned};

macro_rules! error {
    ($err:expr, $span:expr) => {
        Err(Spanned::new($err, $span))
    }
}

pub fn build_texpr_from_id(ty: ty::Type, id: IdentifierId) -> ir::TypedExpression {
    ir::TypedExpression {
        ty: ty::Type::LValue(Box::new(ty)),
        expr: ir::Expression::Identifier(id)
    }
}

pub fn build_assign(lhs: ir::TypedExpression, rhs: ir::TypedExpression) -> ir::TypedExpression {
    let rhs_ty = rhs.ty.clone();
    ir::TypedExpression {
        ty: rhs_ty,
        expr: ir::Expression::Assign {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
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

pub fn lvalue_to_rvalue(expression: ir::TypedExpression) -> ir::TypedExpression {
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

pub fn literal_to_texpr(lit: ir::Literal) -> ir::TypedExpression {
    let ty = match lit {
        ir::Literal::IntLiteral(_) => ty::Type::Int,
        ir::Literal::DoubleLiteral(_) => ty::Type::Double,
        ir::Literal::BooleanLiteral(_) => ty::Type::Boolean,
        ir::Literal::StringLiteral(_) => ty::Type::String,
    };
    ir::TypedExpression {
        ty,
        expr: ir::Expression::Literal(lit)
    }
}
