use typed_arena::Arena;

use trans::symbol_table::{GlobalsTable, SymbolTable};
use ty::TypeContext;

#[derive(Debug, Clone, Default)]
pub struct Context {
    pub ty_arena: Arena<ty::TypeValue>,
}
