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

/*
#[derive(Debug, Clone)]
pub struct TypeContext {
    types: Arena<TypeValue>,
}

macro_rules! get_builtin_type {
    ($name:ident, $ty:tt) => {
        pub fn $name(&self) -> Type {
            self.lookup_type($ty).unwrap()
        }
    }
}

impl Default for TyContext {
    fn default() -> Self {
        TyContext::new()
    }
}

impl TyContext {
    pub fn new() -> TyContext {
        let mut ctxt = TyContext {
            types: Vec::new(),
            names: HashMap::new(),
        };

        ctxt.register_type("void".to_string(), TypeValue::Void);
        ctxt.register_type("int".to_string(), TypeValue::Int);
        ctxt.register_type("double".to_string(), TypeValue::Double);
        ctxt.register_type("boolean".to_string(), TypeValue::Boolean);
        ctxt.register_type("string".to_string(), TypeValue::String);

        ctxt
    }

    fn append_type(&mut self, tv: Option<TypeValue>) -> Type {
        let id = self.types.len();
        self.types.push(tv);
        Type(id)
    }

    fn get_id_from_tv(&mut self, tv: TypeValue) -> Type {
        let mut position = None;
        for (index, vtv) in self.types.iter().enumerate() {
            if let Some(ref vtv) = *vtv {
                if *vtv == tv {
                    position = Some(index);
                    break;
                }
            }
        }

        if let Some(id) = position {
            Type(id)
        } else {
            self.append_type(Some(tv))
        }
    }

    pub fn get_typevalue_from_id(&self, id: Type) -> TypeValue {
        self.types[id.0].clone().unwrap()
    }

    pub fn pre_register_struct_type(&mut self, name: String) -> bool {
        // true if a type with the same name is already defined
        let id = self.append_type(None);
        if let Entry::Vacant(o) = self.names.entry(name) {
            o.insert(id);
            false
        } else {
            true
        }
    }

    pub fn register_struct_type(&mut self, name: &str, tv: TypeValue) {
        let Type(id) = self.lookup_type(name).unwrap();
        self.types[id] = Some(tv);
    }

    fn register_type(&mut self, name: String, tv: TypeValue) {
        // force the insert

        let id = self.append_type(Some(tv));
        self.names.insert(name, id);
    }

    pub fn lookup_type(&self, name: &str) -> Option<Type> {
        self.names.get(name).cloned()
    }

    get_builtin_type!(get_void_ty, "void");
    get_builtin_type!(get_int_ty, "int");
    get_builtin_type!(get_double_ty, "double");
    get_builtin_type!(get_boolean_ty, "boolean");
    get_builtin_type!(get_string_ty, "string");

    pub fn pointer_of(&mut self, ty: Type) -> Type {
        let tv = TypeValue::Pointer(ty);
        self.get_id_from_tv(tv)
    }

    pub fn lvalue_of(&mut self, ty: Type) -> Type {
        let tv = TypeValue::LValue(ty);
        self.get_id_from_tv(tv)
    }

    pub fn is_lvalue(&self, ty: Type) -> Option<Type> {
        if let TypeValue::LValue(sub) = self.get_typevalue_from_id(ty) {
            Some(sub)
        } else {
            None
        }
    }

    pub fn is_pointer(&self, ty: Type) -> Option<Type> {
        if let TypeValue::Pointer(sub) = self.get_typevalue_from_id(ty) {
            Some(sub)
        } else {
            None
        }
    }

    pub fn is_struct(&self, ty: Type) -> Option<StructType> {
        if let TypeValue::Struct(s) = self.get_typevalue_from_id(ty) {
            Some(s)
        } else {
            None
        }
    }

    pub fn is_lvalue_struct(&self, ty: Type) -> Option<StructType> {
        if let Some(sub) = self.is_lvalue(ty) {
            if let Some(s) = self.is_struct(sub) {
                return Some(s);
            }
        }
        None
    }
}*/
