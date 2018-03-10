use std::collections::hash_map::{Entry, HashMap};

use ty;
use ir::IdentifierId;

#[derive(Debug, Default)]
pub struct Tables {
    pub globals: GlobalsTable,
    pub locals: SymbolTable,
    pub types: TypeTable,
}

impl Tables {
    pub fn new_locals(&mut self) {
        self.locals = SymbolTable::new();
    }
}

#[derive(Debug, Clone, Default)]
pub struct GlobalsTable(HashMap<String, ty::FunctionType>);

impl GlobalsTable {
    pub fn register_function(&mut self, name: String, ty: ty::FunctionType) -> bool {
        self.0.insert(name, ty).is_some()
    }

    pub fn lookup_function(&self, name: &str) -> Option<&ty::FunctionType> {
        self.0.get(name)
    }
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub ty: ty::Type,
    pub id: IdentifierId,
}

#[derive(Debug, Clone)]
pub struct SymbolTable {
    id_counter: usize,
    scopes: Vec<HashMap<String, Symbol>>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        SymbolTable::new()
    }
}

impl SymbolTable {
    pub fn new() -> Self {
        SymbolTable {
            id_counter: 0,
            scopes: Vec::new(),
        }
    }

    pub fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn end_scope(&mut self) {
        self.scopes.pop();
    }

    pub fn new_identifier_id(&mut self) -> IdentifierId {
        let identifier_id = IdentifierId(self.id_counter);
        self.id_counter += 1;
        identifier_id
    }

    // return None if the local was already defined
    pub fn register_local(&mut self, name: String, ty: ty::Type) -> Option<IdentifierId> {
        let identifier_id = self.new_identifier_id();
        let symbol = Symbol {
            ty,
            id: identifier_id,
        };

        if self.scopes
            .last_mut()
            .unwrap()
            .insert(name, symbol)
            .is_none()
        {
            Some(identifier_id)
        } else {
            None
        }
    }

    pub fn lookup_local(&self, name: &str) -> Option<&Symbol> {
        for scope in self.scopes.iter().rev() {
            if let Some(t) = scope.get(name) {
                return Some(t);
            }
        }
        None
    }
}

use context::Context;
lazy_static! {
    static ref CONTEXT: Context = Context::new();
}

pub struct TypeTable {
    names: HashMap<String, ty::Type>,
}

macro_rules! get_builtin_type {
    ($name:ident, $ty:tt) => {
        pub fn $name(&self) -> ty::Type {
            self.lookup_type($ty).unwrap()
        }
    }
}

impl Default for TypeTable {
    fn default() -> Self {
        TypeTable::new()
    }
}

use std::fmt;

impl fmt::Debug for TypeTable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TypeTable")
            .field("arena", &"...".to_string())
            .field("names", &self.names)
            .finish()
    }
}

impl TypeTable {
    pub fn new() -> Self {
        let mut table = TypeTable {
            names: HashMap::new(),
        };

        table.register_type("void".to_string(), ty::TypeValue::Void);
        table.register_type("int".to_string(), ty::TypeValue::Int);
        table.register_type("double".to_string(), ty::TypeValue::Double);
        table.register_type("boolean".to_string(), ty::TypeValue::Boolean);
        table.register_type("string".to_string(), ty::TypeValue::String);
        table
    }

    fn append_type(&self, tv: ty::TypeValue) -> ty::Type {
        CONTEXT.get_type(tv)
    }

    fn register_type(&mut self, name: String, tv: ty::TypeValue) {
        // force the insert
        let ty = CONTEXT.get_type(tv);
        self.names.insert(name, ty);
    }

    pub fn lookup_type(&self, name: &str) -> Option<ty::Type> {
        self.names.get(name).cloned()
    }

    get_builtin_type!(get_void_ty, "void");
    get_builtin_type!(get_int_ty, "int");
    get_builtin_type!(get_double_ty, "double");
    get_builtin_type!(get_boolean_ty, "boolean");
    get_builtin_type!(get_string_ty, "string");

    pub fn pre_register_struct_type(&mut self, name: String) -> bool {
        // true if a type with the same name is already defined
        let ty = self.append_type(ty::TypeValue::Incomplete);
        if let Entry::Vacant(o) = self.names.entry(name) {
            o.insert(ty);
            false
        } else {
            true
        }
    }

    pub fn register_struct_type(&mut self, name: &str, struct_tv: ty::StructTypeValue) -> bool {
        // return true if struct cycle
        let mut ty = self.lookup_type(name).unwrap();
        if has_cycles(&struct_tv, ty) {
            true
        } else {
            *ty = ty::TypeValue::Struct(CONTEXT.alloc_struct_type(struct_tv));
            false
        }
    }

    pub fn lvalue_of(&self, sub_ty: ty::Type, assignable: bool) -> ty::Type {
        let tv = ty::TypeValue::LValue(sub_ty, assignable);
        CONTEXT.get_type(tv)
    }

    pub fn pointer_of(&self, sub_ty: ty::Type) -> ty::Type {
        let tv = ty::TypeValue::Pointer(sub_ty);
        CONTEXT.get_type(tv)
    }

    pub fn array_of(&self, sub_ty: ty::Type, size: usize) -> ty::Type {
        let tv = ty::TypeValue::Array(sub_ty, size);
        CONTEXT.get_type(tv)
    }

    pub fn function_of(&self, func_ty: ty::FunctionType) -> ty::Type {
        let tv = ty::TypeValue::FunctionPtr(func_ty);
        CONTEXT.get_type(tv)
    }

    pub fn tuple_of(&self, types: Vec<ty::Type>) -> ty::Type {
        let tv = ty::TypeValue::Tuple(types);
        CONTEXT.get_type(tv)
    }
}

fn has_cycles(struct_tv: &ty::StructTypeValue, ty: ty::Type) -> bool {
    for &(_, field_ty) in &struct_tv.fields {
        if field_ty == ty {
            return true;
        }

        if let ty::TypeValue::Struct(ref stv) = *field_ty {
            if has_cycles(stv, ty) {
                return true;
            }
        }
    }
    false
}
