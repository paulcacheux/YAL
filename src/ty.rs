use std::collections::hash_map::{Entry, HashMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Type(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeValue {
    Int,
    Double,
    Boolean,
    String,
    Void,
    // Struct(StructType),
    LValue(Type),
    Pointer(Type),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructType {
    pub fields: Vec<(String, Type)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub return_ty: Type,
    pub parameters_ty: Vec<Type>,
    pub is_vararg: bool,
}

#[derive(Debug, Clone)]
pub struct TyContext {
    types: Vec<TypeValue>,
    names: HashMap<String, Type>,
}

macro_rules! get_builtin_type {
    ($name:ident, $ty:tt) => {
        pub fn $name(&self) -> Type {
            self.lookup_type($ty).unwrap()
        }
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

    fn get_id_from_tv(&mut self, tv: TypeValue) -> Type {
        if let Some(id) = self.types.iter().position(|vtv| *vtv == tv) {
            Type(id)
        } else {
            let id = self.types.len();
            self.types.push(tv);
            Type(id)
        }
    }

    pub fn get_typevalue_from_id(&self, id: Type) -> TypeValue {
        self.types[id.0].clone()
    }

    pub fn register_type(&mut self, name: String, tv: TypeValue) -> Option<Type> {
        // None if a type with the same name is already defined

        let ty_id = self.get_id_from_tv(tv);
        if let Entry::Vacant(o) = self.names.entry(name) {
            o.insert(ty_id);
            Some(ty_id)
        } else {
            None
        }
    }

    pub fn lookup_type(&self, name: &str) -> Option<Type> {
        self.names.get(name).map(|t| *t)
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
}
