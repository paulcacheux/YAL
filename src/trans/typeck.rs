use ty;
use ast;
use ir;

pub fn binop_typeck(
    binop: ast::BinaryOperatorKind,
    lhs: &ty::Type,
    rhs: &ty::Type,
) -> Option<(ty::Type, ir::BinaryOperatorKind)> {
    use ast::BinaryOperatorKind::*;
    match (binop, lhs, rhs) {
        (Plus, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntPlus))
        }
        (Plus, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Double, ir::BinaryOperatorKind::DoublePlus))
        }
        (Minus, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntMinus))
        }
        (Minus, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Double, ir::BinaryOperatorKind::DoubleMinus))
        }
        (Multiply, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntMultiply))
        }
        (Multiply, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Double, ir::BinaryOperatorKind::DoubleMultiply))
        }
        (Divide, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntDivide))
        }
        (Divide, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Double, ir::BinaryOperatorKind::DoubleDivide))
        }
        (Modulo, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::IntModulo))
        }

        (Equal, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntEqual))
        }
        (Equal, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleEqual))
        }
        (Equal, &ty::Type::Boolean, &ty::Type::Boolean) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::BooleanEqual))
        }

        (NotEqual, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntNotEqual))
        }
        (NotEqual, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleNotEqual))
        }
        (NotEqual, &ty::Type::Boolean, &ty::Type::Boolean) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::BooleanNotEqual))
        }

        (Less, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntLess))
        }
        (Less, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleLess))
        }

        (LessEqual, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntLessEqual))
        }
        (LessEqual, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleLessEqual))
        }

        (Greater, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntGreater))
        }
        (Greater, &ty::Type::Double, &ty::Type::Double) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::DoubleGreater))
        }

        (GreaterEqual, &ty::Type::Int, &ty::Type::Int) => {
            Some((ty::Type::Boolean, ir::BinaryOperatorKind::IntGreaterEqual))
        }
        (GreaterEqual, &ty::Type::Double, &ty::Type::Double) => Some((
            ty::Type::Boolean,
            ir::BinaryOperatorKind::DoubleGreaterEqual,
        )),
        (Plus, &ty::Type::Pointer(ref sub), &ty::Type::Int) => {
            Some((*sub.clone(), ir::BinaryOperatorKind::PtrPlusOffset))
        }
        (Minus, &ty::Type::Pointer(ref sub), &ty::Type::Int) => {
            Some((*sub.clone(), ir::BinaryOperatorKind::PtrMinusOffset))
        }
        (Minus, &ty::Type::Pointer(ref a), &ty::Type::Pointer(ref b)) if *a == *b => {
            Some((ty::Type::Int, ir::BinaryOperatorKind::PtrDiff))
        }
        _ => None,
    }
}

pub fn unop_typeck(
    unop: ast::UnaryOperatorKind,
    sub: &ty::Type,
) -> Option<(ty::Type, ir::UnaryOperatorKind)> {
    use ast::UnaryOperatorKind::*;

    match (unop, sub) {
        (Minus, &ty::Type::Int) => Some((ty::Type::Int, ir::UnaryOperatorKind::IntMinus)),
        (Minus, &ty::Type::Double) => Some((ty::Type::Double, ir::UnaryOperatorKind::DoubleMinus)),
        (LogicalNot, &ty::Type::Boolean) => {
            Some((ty::Type::Boolean, ir::UnaryOperatorKind::BooleanNot))
        }
        (PtrDeref, &ty::Type::Pointer(ref sub)) if **sub != ty::Type::Void => Some((
            ty::Type::LValue(sub.clone()),
            ir::UnaryOperatorKind::PointerDeref,
        )),
        _ => None,
    }
}

pub fn lvalue_unop_typeck(
    lvalue_unop: ast::LValueUnaryOperatorKind,
    sub: &ty::Type,
) -> Option<(ty::Type, ir::LValueUnaryOperatorKind)> {
    use ast::LValueUnaryOperatorKind::*;

    match (lvalue_unop, sub) {
        (Increment, &ty::Type::Int) => Some((
            ty::Type::LValue(Box::new(ty::Type::Int)),
            ir::LValueUnaryOperatorKind::IntIncrement,
        )),
        (Decrement, &ty::Type::Int) => Some((
            ty::Type::LValue(Box::new(ty::Type::Int)),
            ir::LValueUnaryOperatorKind::IntDecrement,
        )),
        (AddressOf, sub) => Some((
            ty::Type::Pointer(Box::new(sub.clone())),
            ir::LValueUnaryOperatorKind::LValueToPtr,
        )),
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub enum CastTypeckResult {
    Cast(ir::CastKind),
    BitCast,
    Error,
}

pub fn cast_typeck(src_ty: &ty::Type, target_ty: &ty::Type) -> CastTypeckResult {
    use self::CastTypeckResult::*;
    match (src_ty, target_ty) {
        (&ty::Type::Int, &ty::Type::Double) => Cast(ir::CastKind::IntToDouble),
        (&ty::Type::Double, &ty::Type::Int) => Cast(ir::CastKind::DoubleToInt),
        (&ty::Type::Boolean, &ty::Type::Int) => Cast(ir::CastKind::BooleanToInt),
        (&ty::Type::Int, &ty::Type::Boolean) => Cast(ir::CastKind::IntToBoolean),
        (&ty::Type::Pointer(_), &ty::Type::Pointer(_)) => BitCast,
        (a, b) if a == b => BitCast,
        _ => Error,
    }
}
