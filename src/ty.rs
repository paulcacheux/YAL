use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

macro_rules! wrapper {
    ($name:ident -> $sub_ty:ty) => {

        #[derive(Debug, Clone, Copy)]
        pub struct $name(*mut $sub_ty);

        impl $name {
            pub fn from_raw(sub: *mut $sub_ty) -> Self {
                $name(sub)
            }
        }

        unsafe impl Send for $name {}

        impl Deref for $name {
            type Target = $sub_ty;

            fn deref(&self) -> &Self::Target {
                unsafe { &*self.0 }
            }
        }

        impl DerefMut for $name {
            fn deref_mut(&mut self) -> &mut Self::Target {
                unsafe { &mut *self.0 }
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                **self == **other
            }
        }

        impl Eq for $name {}

        impl Hash for $name {
            fn hash<H: Hasher>(&self, state: &mut H) {
                (**self).hash(state);
            }
        }
    }
}

wrapper!(Type -> TypeValue);
wrapper!(StructType -> StructTypeValue);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeValue {
    Incomplete,
    Int,
    Double,
    Boolean,
    String,
    Void,
    Struct(StructType),
    LValue(Type, bool), // assignable
    Pointer(Type),
    Array(Type, usize),
}

impl TypeValue {
    pub fn has_field(&self, field_name: &str) -> Option<(usize, Type)> {
        match *self {
            TypeValue::Struct(st) => {
                for (index, &(ref name, ty)) in st.fields.iter().enumerate() {
                    if name == field_name {
                        return Some((index, ty));
                    }
                }
                None
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructTypeValue {
    pub name: String,
    pub fields: Vec<(String, Type)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub return_ty: Type,
    pub parameters_ty: Vec<Type>,
    pub is_vararg: bool,
}
