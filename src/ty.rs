#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Double,
    Boolean,
    String,
    Void,
    StructPointer(String),
    LValue(Box<Type>),
    Array(Box<Type>)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub return_ty: Type,
    pub parameters_ty: Vec<Type>,
}
