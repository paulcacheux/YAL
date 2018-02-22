use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::fmt;

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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match **self {
            TypeValue::Incomplete => write!(f, "incomplete"),
            TypeValue::Int => write!(f, "int"),
            TypeValue::Double => write!(f, "double"),
            TypeValue::Boolean => write!(f, "boolean"),
            TypeValue::String => write!(f, "string"),
            TypeValue::Void => write!(f, "void"),
            TypeValue::Pointer(ref sub) => write!(f, "*{}", sub),
            TypeValue::Struct(ref s) => write!(f, "struct {} {{ .. }}", s.name),
            TypeValue::Array(ref sub, ref size) => write!(f, "[{}; {}]", sub, size),
            _ => panic!("Type not supposed to be displayed"),
        }
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
    LValue(Type, bool), // assignable
    Pointer(Type),
    Array(Type, usize),
}

#[derive(Debug, Clone)]
pub enum FieldInfo {
    StructField(usize, Type),
    ArrayLen(usize),
}

impl TypeValue {
    pub fn has_field(&self, field_name: &str) -> Option<FieldInfo> {
        match *self {
            TypeValue::Struct(st) => {
                for (index, &(ref name, ty)) in st.fields.iter().enumerate() {
                    if name == field_name {
                        return Some(FieldInfo::StructField(index, ty));
                    }
                }
                None
            }
            TypeValue::Array(_, size) => {
                if field_name == "len" {
                    Some(FieldInfo::ArrayLen(size))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Eq)]
pub struct StructTypeValue {
    pub name: String,
    pub fields: Vec<(String, Type)>,
}

impl PartialEq for StructTypeValue {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name // currently we eq on name because we don't have any module/namespace. Maybe use an id
    }
}

impl Hash for StructTypeValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub return_ty: Type,
    pub parameters_ty: Vec<Type>,
    pub is_vararg: bool,
}
