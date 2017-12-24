use std::collections::HashMap;

use ty;

#[derive(Debug, Clone)]
pub struct GlobalsTable(HashMap<String, ty::FunctionType>);

impl GlobalsTable {
    pub fn new() -> GlobalsTable {
        GlobalsTable(HashMap::new())
    }

    pub fn register_function(&mut self, name: String, ty: ty::FunctionType) -> bool {
        self.0.insert(name, ty).is_some()
    }

    pub fn lookup_function(&self, name: &String) -> Option<&ty::FunctionType> {
        self.0.get(name)
    }
}

#[derive(Debug, Clone)]
pub struct SymbolTable<'g> {
    globals: &'g GlobalsTable,
    scopes: Vec<HashMap<String, ty::Type>>,
}

impl<'g> SymbolTable<'g> {
    pub fn new(globals: &GlobalsTable) -> SymbolTable {
        SymbolTable {
            globals,
            scopes: Vec::new(),
        }
    }

    pub fn lookup_function(&self, name: &String) -> Option<&ty::FunctionType> {
        self.globals.lookup_function(name)
    }

    pub fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn end_scope(&mut self) {
        self.scopes.pop();
    }

    // return true if the function was already defined
    pub fn register_local(&mut self, name: String, ty: ty::Type) -> bool {
        self.scopes.last_mut().unwrap().insert(name, ty).is_some()
    }

    pub fn lookup_local(&self, name: &String) -> Option<&ty::Type> {
        for scope in self.scopes.iter().rev() {
            if let Some(t) = scope.get(name) {
                return Some(t)
            }
        }
        None
    }
}
