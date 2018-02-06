use std::collections::HashMap;

use ty;
use ir::IdentifierId;

#[derive(Debug, Clone)]
pub struct GlobalsTable(HashMap<String, ty::FunctionType>);

impl GlobalsTable {
    pub fn new() -> GlobalsTable {
        GlobalsTable(HashMap::new())
    }

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

impl SymbolTable {
    pub fn new() -> SymbolTable {
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
