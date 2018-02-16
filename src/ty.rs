use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, Copy)]
pub struct Type(*mut TypeValue);

impl Type {
    pub fn from_raw(tv: *mut TypeValue) -> Self {
        Type(tv)
    }
}

unsafe impl Send for Type {}

use std::ops::{Deref, DerefMut};

impl Deref for Type {
    type Target = TypeValue;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0 }
    }
}

impl DerefMut for Type {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.0 }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Type) -> bool {
        **self == **other
    }
}

impl Eq for Type {}

impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeValue {
    Incomplete,
    Int,
    Double,
    Boolean,
    String,
    Void,
    Struct(StructType),
    LValue(Type),
    Pointer(Type),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructType {
    pub name: String,
    pub fields: Vec<(String, Type)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub return_ty: Type,
    pub parameters_ty: Vec<Type>,
    pub is_vararg: bool,
}
