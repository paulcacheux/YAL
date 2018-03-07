use std::collections::HashMap;

use ty;
use ir;
use common;
use ir::IdentifierId;
use errors::TranslationError;
use trans::{self, typeck, TranslationResult};
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
    let value = ir::Value::Local(id);
    ir::Expression::Assign {
        lhs: Box::new(ir::Expression::Value(value)),
        rhs: Box::new(rhs),
    }
}

pub fn build_assign_to_field(
    struct_expr: ir::Expression,
    index: usize,
    expr: ir::Expression,
) -> ir::Expression {
    ir::Expression::Assign {
        lhs: Box::new(ir::Expression::FieldAccess {
            sub: Box::new(struct_expr),
            index,
        }),
        rhs: Box::new(expr),
    }
}

pub fn build_assign_to_array_index(
    ptr: ir::Expression,
    index: usize,
    expr: ir::Expression,
) -> ir::Expression {
    ir::Expression::Assign {
        lhs: Box::new(build_subscript(
            ptr,
            ir::Expression::Value(ir::Value::Literal(common::Literal::IntLiteral(index as _))),
        )),
        rhs: Box::new(expr),
    }
}

pub fn build_subscript(ptr: ir::Expression, index: ir::Expression) -> ir::Expression {
    ir::Expression::UnaryOperator {
        unop: ir::UnaryOperatorKind::PointerDeref,
        sub: Box::new(ir::Expression::BinaryOperator {
            binop: ir::BinaryOperatorKind::PtrPlusOffset,
            lhs: Box::new(ptr),
            rhs: Box::new(index),
        }),
    }
}

pub fn check_eq_types_auto_cast(
    expr: TypedExpression,
    target_ty: ty::Type,
    error_span: Span,
) -> TranslationResult<TypedExpression> {
    match typeck::auto_cast(expr.ty, target_ty) {
        typeck::CastTypeckResult::Cast(kind) => Ok(TypedExpression {
            ty: target_ty,
            expr: ir::Expression::Cast {
                kind,
                sub: Box::new(expr.expr),
            },
        }),
        typeck::CastTypeckResult::BitCast => Ok(TypedExpression {
            ty: target_ty,
            expr: ir::Expression::BitCast {
                dest_ty: target_ty,
                sub: Box::new(expr.expr),
            },
        }),
        typeck::CastTypeckResult::None => {
            check_eq_types(expr.ty, target_ty, error_span)?;
            Ok(expr)
        }
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

pub fn lvalue_to_rvalue(expression: TypedExpression) -> TypedExpression {
    if let ty::TypeValue::LValue(sub, _) = *expression.ty {
        TypedExpression {
            ty: sub,
            expr: ir::Expression::LValueToRValue(Box::new(expression.expr)),
        }
    } else {
        expression
    }
}

pub fn rvalue_to_lvalue(
    ty_table: &trans::tables::TypeTable,
    expression: TypedExpression,
) -> (TypedExpression, ty::Type) {
    if let ty::TypeValue::LValue(sub_ty, _) = *expression.ty {
        (expression, sub_ty)
    } else {
        let sub_ty = expression.ty;
        (
            TypedExpression {
                ty: ty_table.lvalue_of(sub_ty, false),
                expr: ir::Expression::RValueToLValue(Box::new(expression.expr)),
            },
            sub_ty,
        )
    }
}

pub fn unsure_subscriptable(
    type_table: &trans::tables::TypeTable,
    expr: TypedExpression,
) -> Option<(ty::Type, ir::Expression)> {
    let expr = if let ty::TypeValue::LValue(sub, _) = *expr.ty {
        if let ty::TypeValue::Array(sub, _) = *sub {
            let ptr = ir::Expression::BitCast {
                dest_ty: type_table.pointer_of(sub),
                sub: Box::new(expr.expr),
            };
            return Some((sub, ptr));
        } else {
            lvalue_to_rvalue(expr)
        }
    } else {
        expr
    };

    if let ty::TypeValue::Pointer(sub) = *expr.ty {
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
            ir::Expression::Value(ir::Value::Literal(common::Literal::BooleanLiteral(true))) => {
                check_return_paths(body)
            }
            ir::Expression::Value(ir::Value::Literal(common::Literal::BooleanLiteral(false))) => {
                check_return_paths(else_clause)
            }
            _ => check_return_paths(body) && check_return_paths(else_clause),
        },
        ir::Statement::For { ref condition, .. } => {
            if let ir::Expression::Value(ir::Value::Literal(common::Literal::BooleanLiteral(
                true,
            ))) = *condition
            {
                true
            } else {
                false
            }
        }
        ir::Statement::Return(_) => true,
        _ => false,
    }
}

#[derive(Debug)]
pub struct StructLitChecker {
    struct_name: String,
    fields: HashMap<String, (ty::Type, usize, bool)>,
    span: Span,
}

impl StructLitChecker {
    pub fn new(value: ty::StructTypeValue, span: Span) -> Self {
        let mut fields = HashMap::new();
        for (index, (f_name, f_ty)) in value.fields.into_iter().enumerate() {
            fields.insert(f_name, (f_ty, index, false));
        }

        StructLitChecker {
            struct_name: value.name,
            fields,
            span,
        }
    }

    pub fn set_field(
        &mut self,
        field: &str,
        expr: TypedExpression,
        span: Span,
    ) -> TranslationResult<(TypedExpression, usize)> {
        if let Some(&mut (ty, index, ref mut set)) = self.fields.get_mut(field) {
            if *set {
                return error!(TranslationError::FieldAreadySet(field.to_string()), span);
            }
            let expr = check_eq_types_auto_cast(expr, ty, span)?;
            check_eq_types(ty, expr.ty, span)?;
            *set = true;
            Ok((expr, index))
        } else {
            error!(TranslationError::UndefinedField(field.to_string()), span)
        }
    }

    pub fn final_check(self) -> TranslationResult<()> {
        for &(_, _, set) in self.fields.values() {
            if !set {
                return error!(TranslationError::FieldNotSet, self.span);
            }
        }
        Ok(())
    }
}
