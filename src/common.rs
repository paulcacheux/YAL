use interner::InternerId;
use ty;
use trans::tables::TypeTable;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Literal {
    IntLiteral(i64),
    DoubleLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(InternerId),
}

impl Literal {
    pub fn get_type(&self, ty_ctxt: &TypeTable) -> ty::Type {
        use self::Literal::*;
        match *self {
            IntLiteral(_) => ty_ctxt.get_int_ty(),
            DoubleLiteral(_) => ty_ctxt.get_double_ty(),
            BooleanLiteral(_) => ty_ctxt.get_boolean_ty(),
            StringLiteral(_) => ty_ctxt.get_string_ty(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Field {
    Named(String),
    Index(usize),
}

use std::fmt;
impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Field::Named(ref s) => s.fmt(f),
            Field::Index(i) => write!(f, "{}", i),
        }
    }
}
