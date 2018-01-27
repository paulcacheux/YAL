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
    pub fn get_type(&self) -> ty::Type {
        use self::Literal::*;
        match *self {
            IntLiteral(_) => ty::Type::Int,
            DoubleLiteral(_) => ty::Type::Double,
            BooleanLiteral(_) => ty::Type::Boolean,
            StringLiteral(_) => ty::Type::String,
        }
    }
}
