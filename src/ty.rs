#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Double,
    Boolean,
    String,
    Void,
    StructPointer(String),
    LValue(Box<Type>),
    Array(Box<Type>),
    Pointer(Box<Type>),
}

impl Type {
    pub fn has_default_value(&self) -> bool {
        match *self {
            Type::Int | Type::Double | Type::Boolean => true,
            _ => false,
        }
    }

    pub fn is_invalid(&self) -> bool {
        match *self {
            Type::LValue(ref sub) | Type::Array(ref sub) => **sub == Type::Void || sub.is_invalid(),
            Type::Pointer(ref sub) => sub.is_invalid(),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub return_ty: Type,
    pub parameters_ty: Vec<Type>,
    pub is_vararg: bool,
}
