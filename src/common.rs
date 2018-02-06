use interner::InternerId;
use ty;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Literal {
    IntLiteral(i64),
    DoubleLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(InternerId),
}

impl Literal {
    pub fn get_type(&self, ty_ctxt: &ty::TyContext) -> ty::Type {
        use self::Literal::*;
        match *self {
            IntLiteral(_) => ty_ctxt.get_int_ty(),
            DoubleLiteral(_) => ty_ctxt.get_double_ty(),
            BooleanLiteral(_) => ty_ctxt.get_boolean_ty(),
            StringLiteral(_) => ty_ctxt.get_string_ty(),
        }
    }
}
