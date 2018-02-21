use ty;
use ast;
use ir;
use trans;

pub fn binop_typeck(
    type_ctxt: &trans::tables::TypeTable,
    binop: ast::BinaryOperatorKind,
    lhs: ty::Type,
    rhs: ty::Type,
) -> Option<(ty::Type, ir::BinaryOperatorKind)> {
    let int_ty = type_ctxt.get_int_ty();
    let double_ty = type_ctxt.get_double_ty();
    let bool_ty = type_ctxt.get_boolean_ty();

    use ast::BinaryOperatorKind::*;
    match (binop, &*lhs, &*rhs) {
        (Plus, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((int_ty, ir::BinaryOperatorKind::IntPlus))
        }
        (Plus, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((double_ty, ir::BinaryOperatorKind::DoublePlus))
        }
        (Minus, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((int_ty, ir::BinaryOperatorKind::IntMinus))
        }
        (Minus, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((double_ty, ir::BinaryOperatorKind::DoubleMinus))
        }
        (Multiply, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((int_ty, ir::BinaryOperatorKind::IntMultiply))
        }
        (Multiply, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((double_ty, ir::BinaryOperatorKind::DoubleMultiply))
        }
        (Divide, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((int_ty, ir::BinaryOperatorKind::IntDivide))
        }
        (Divide, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((double_ty, ir::BinaryOperatorKind::DoubleDivide))
        }
        (Modulo, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((int_ty, ir::BinaryOperatorKind::IntModulo))
        }

        (Equal, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((bool_ty, ir::BinaryOperatorKind::IntEqual))
        }
        (Equal, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((bool_ty, ir::BinaryOperatorKind::DoubleEqual))
        }
        (Equal, &ty::TypeValue::Boolean, &ty::TypeValue::Boolean) => {
            Some((bool_ty, ir::BinaryOperatorKind::BooleanEqual))
        }

        (NotEqual, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((bool_ty, ir::BinaryOperatorKind::IntNotEqual))
        }
        (NotEqual, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((bool_ty, ir::BinaryOperatorKind::DoubleNotEqual))
        }
        (NotEqual, &ty::TypeValue::Boolean, &ty::TypeValue::Boolean) => {
            Some((bool_ty, ir::BinaryOperatorKind::BooleanNotEqual))
        }

        (Less, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((bool_ty, ir::BinaryOperatorKind::IntLess))
        }
        (Less, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((bool_ty, ir::BinaryOperatorKind::DoubleLess))
        }

        (LessEqual, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((bool_ty, ir::BinaryOperatorKind::IntLessEqual))
        }
        (LessEqual, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((bool_ty, ir::BinaryOperatorKind::DoubleLessEqual))
        }

        (Greater, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((bool_ty, ir::BinaryOperatorKind::IntGreater))
        }
        (Greater, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((bool_ty, ir::BinaryOperatorKind::DoubleGreater))
        }

        (GreaterEqual, &ty::TypeValue::Int, &ty::TypeValue::Int) => {
            Some((bool_ty, ir::BinaryOperatorKind::IntGreaterEqual))
        }
        (GreaterEqual, &ty::TypeValue::Double, &ty::TypeValue::Double) => {
            Some((bool_ty, ir::BinaryOperatorKind::DoubleGreaterEqual))
        }
        (Plus, &ty::TypeValue::Pointer(sub), &ty::TypeValue::Int) => {
            Some((sub, ir::BinaryOperatorKind::PtrPlusOffset))
        }
        (Minus, &ty::TypeValue::Pointer(sub), &ty::TypeValue::Int) => {
            Some((sub, ir::BinaryOperatorKind::PtrMinusOffset))
        }
        (Minus, &ty::TypeValue::Pointer(a), &ty::TypeValue::Pointer(b)) if a == b => {
            Some((int_ty, ir::BinaryOperatorKind::PtrDiff))
        }
        _ => None,
    }
}

pub fn unop_typeck(
    type_ctxt: &trans::tables::TypeTable,
    unop: ast::UnaryOperatorKind,
    sub: ty::Type,
) -> Option<(ty::Type, ir::UnaryOperatorKind)> {
    let int_ty = type_ctxt.get_int_ty();
    let double_ty = type_ctxt.get_double_ty();
    let bool_ty = type_ctxt.get_boolean_ty();
    let void_ty = type_ctxt.get_void_ty();

    use ast::UnaryOperatorKind::*;
    match (unop, &*sub) {
        (Minus, &ty::TypeValue::Int) => Some((int_ty, ir::UnaryOperatorKind::IntMinus)),
        (Minus, &ty::TypeValue::Double) => Some((double_ty, ir::UnaryOperatorKind::DoubleMinus)),
        (LogicalNot, &ty::TypeValue::Boolean) => Some((bool_ty, ir::UnaryOperatorKind::BooleanNot)),
        (PtrDeref, &ty::TypeValue::Pointer(sub)) if sub != void_ty => Some((
            type_ctxt.lvalue_of(sub, true),
            ir::UnaryOperatorKind::PointerDeref,
        )),
        _ => None,
    }
}

pub fn lvalue_unop_typeck(
    type_ctxt: &trans::tables::TypeTable,
    lvalue_unop: ast::LValueUnaryOperatorKind,
    sub: ty::Type,
) -> Option<(ty::Type, ir::LValueUnaryOperatorKind)> {
    let int_ty = type_ctxt.get_int_ty();

    use ast::LValueUnaryOperatorKind::*;
    match (lvalue_unop, &*sub) {
        (Increment, &ty::TypeValue::Int) => Some((
            type_ctxt.lvalue_of(int_ty, true),
            ir::LValueUnaryOperatorKind::IntIncrement,
        )),
        (Decrement, &ty::TypeValue::Int) => Some((
            type_ctxt.lvalue_of(int_ty, true),
            ir::LValueUnaryOperatorKind::IntDecrement,
        )),
        (AddressOf, _) => Some((
            type_ctxt.pointer_of(sub), // the function parameter
            ir::LValueUnaryOperatorKind::LValueToPtr,
        )),
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub enum CastTypeckResult {
    Cast(ir::CastKind),
    BitCast,
    None,
}

pub fn cast_typeck(src_ty: ty::Type, target_ty: ty::Type) -> CastTypeckResult {
    use self::CastTypeckResult::*;
    match (&*src_ty, &*target_ty) {
        (&ty::TypeValue::Int, &ty::TypeValue::Double) => Cast(ir::CastKind::IntToDouble),
        (&ty::TypeValue::Double, &ty::TypeValue::Int) => Cast(ir::CastKind::DoubleToInt),
        (&ty::TypeValue::Boolean, &ty::TypeValue::Int) => Cast(ir::CastKind::BooleanToInt),
        (&ty::TypeValue::Int, &ty::TypeValue::Boolean) => Cast(ir::CastKind::IntToBoolean),
        (&ty::TypeValue::Pointer(_), &ty::TypeValue::Int) => Cast(ir::CastKind::PtrToInt),
        (&ty::TypeValue::Int, &ty::TypeValue::Pointer(_)) => {
            Cast(ir::CastKind::IntToPtr(target_ty))
        }
        (&ty::TypeValue::Pointer(_), &ty::TypeValue::Pointer(_)) => BitCast,
        (ref a, ref b) if a == b => BitCast,
        _ => None,
    }
}

pub fn auto_cast(src_ty: ty::Type, target_ty: ty::Type) -> CastTypeckResult {
    use self::CastTypeckResult::*;
    match (&*src_ty, &*target_ty) {
        (&ty::TypeValue::Pointer(src), &ty::TypeValue::Pointer(_)) => {
            if let ty::TypeValue::Void = *src {
                BitCast
            } else {
                None
            }
        }
        _ => None,
    }
}
