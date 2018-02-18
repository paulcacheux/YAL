use std::collections::HashMap;

use ty;
use ir;
use common;
use ir::IdentifierId;
use errors::TranslationError;
use trans::{self, TranslationResult};
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
) -> TypedExpression {
    if let ty::TypeValue::LValue(_, _) = *expression.ty {
        expression
    } else {
        TypedExpression {
            ty: ty_table.lvalue_of(expression.ty, false),
            expr: ir::Expression::RValueToLValue(Box::new(expression.expr)),
        }
    }
}

pub fn unsure_subscriptable(expr: TypedExpression) -> Option<(ty::Type, ir::Expression)> {
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
            ir::Expression::Literal(common::Literal::BooleanLiteral(true)) => {
                check_return_paths(body)
            }
            ir::Expression::Literal(common::Literal::BooleanLiteral(false)) => {
                check_return_paths(else_clause)
            }
            _ => check_return_paths(body) && check_return_paths(else_clause),
        },
        ir::Statement::For { ref condition, .. } => {
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
        expr_ty: ty::Type,
        span: Span,
    ) -> TranslationResult<usize> {
        if let Some(&mut (ty, index, ref mut set)) = self.fields.get_mut(field) {
            if *set {
                return error!(TranslationError::FieldAreadySet(field.to_string()), span);
            }
            check_eq_types(ty, expr_ty, span)?;
            *set = true;
            Ok(index)
        } else {
            error!(
                TranslationError::UndefinedField(field.to_string(), self.struct_name.clone()),
                span
            )
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
