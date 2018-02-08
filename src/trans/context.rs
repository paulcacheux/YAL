use trans::symbol_table::{GlobalsTable, SymbolTable};
use ty::TyContext;

#[derive(Debug, Clone, Default)]
pub struct Context {
    pub globals: GlobalsTable,
    pub locals: SymbolTable,
    pub types: TyContext,
}

impl Context {
    pub fn new_locals(&mut self) {
        self.locals = SymbolTable::new();
    }
}
