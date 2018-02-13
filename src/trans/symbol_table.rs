use std::collections::HashMap;

use typed_arena::Arena;

use ty;
use ir::IdentifierId;

#[derive(Debug, Clone, Default)]
pub struct Tables<'ctxt> {
    pub globals: GlobalsTable<'ctxt>,
    pub locals: SymbolTable<'ctxt>,
    pub types: TypeTable<'ctxt>,
}

impl<'ctxt> Tables<'ctxt> {
    pub fn new_locals(&mut self) {
        self.locals = SymbolTable::new();
    }
}

#[derive(Debug, Clone, Default)]
pub struct GlobalsTable<'ctxt>(HashMap<String, ty::FunctionType<'ctxt>>);

impl<'ctxt> GlobalsTable<'ctxt> {
    pub fn register_function(&mut self, name: String, ty: ty::FunctionType<'ctxt>) -> bool {
        self.0.insert(name, ty).is_some()
    }

    pub fn lookup_function(&self, name: &str) -> Option<&ty::FunctionType<'ctxt>> {
        self.0.get(name)
    }
}

#[derive(Debug, Clone)]
pub struct Symbol<'ctxt> {
    pub ty: ty::Type<'ctxt>,
    pub id: IdentifierId,
}

#[derive(Debug, Clone)]
pub struct SymbolTable<'ctxt> {
    id_counter: usize,
    scopes: Vec<HashMap<String, Symbol<'ctxt>>>,
}

impl<'ctxt> Default for SymbolTable<'ctxt> {
    fn default() -> Self {
        SymbolTable::new()
    }
}

impl<'ctxt> SymbolTable<'ctxt> {
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

#[derive(Clone)]
pub struct TypeTable<'ctxt> {
    arena: &'ctxt Arena<ty::TypeValue<'ctxt>>,
    names: HashMap<String, &'ctxt mut ty::TypeValue<'ctxt>>,
}

macro_rules! get_builtin_type {
    ($name:ident, $ty:tt) => {
        pub fn $name(&self) -> ty::Type<'ctxt> {
            self.lookup_type($ty).unwrap()
        }
    }
}

impl<'ctxt> TypeTable<'ctxt> {
    pub fn new(arena: &'ctxt Arena<ty::TypeValue<'ctxt>>) -> Self {
        let mut table = TypeTable {
            arena,
            names: HashMap::new(),
        };

        table.register_type("void".to_string(), ty::TypeValue::Void);
        table.register_type("int".to_string(), ty::TypeValue::Int);
        table.register_type("double".to_string(), ty::TypeValue::Double);
        table.register_type("boolean".to_string(), ty::TypeValue::Boolean);
        table.register_type("string".to_string(), ty::TypeValue::String);
        table
    }

    fn register_type(&mut self, name: String, tv: ty::TypeValue) {
        // force the insert
        let ty = self.arena.alloc(tv);
        self.names.insert(name, tv);
    }

    pub fn lookup_type(&self, name: &str) -> Option<ty::Type<'ctxt>> {
        self.names.get(name).cloned()
    }

    get_builtin_type!(get_void_ty, "void");
    get_builtin_type!(get_int_ty, "int");
    get_builtin_type!(get_double_ty, "double");
    get_builtin_type!(get_boolean_ty, "boolean");
    get_builtin_type!(get_string_ty, "string");
}
