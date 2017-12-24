#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int,
    Double,
    Boolean,
    String,
    Void,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QualifiedType {
    pub ty: Type,
    pub lvalue: bool,
}

impl QualifiedType {
    pub fn new(ty: Type, lvalue: bool) -> Self {
        QualifiedType { ty, lvalue }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub return_ty: Type,
    pub parameters_ty: Vec<Type>,
}
