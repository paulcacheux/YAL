use typed_arena::Arena;

use std::sync::Mutex;
use std::collections::hash_map::{Entry, HashMap};

use ty;

pub struct Context {
    ty_arena: Mutex<Arena<ty::TypeValue>>,
    ty_interner: Mutex<HashMap<ty::TypeValue, ty::Type>>,
    struct_arena: Mutex<Arena<ty::StructTypeValue>>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            ty_arena: Mutex::new(Arena::new()),
            ty_interner: Mutex::new(HashMap::new()),
            struct_arena: Mutex::new(Arena::new()),
        }
    }

    pub fn get_type(&self, value: ty::TypeValue) -> ty::Type {
        match self.ty_interner.lock().unwrap().entry(value.clone()) {
            Entry::Occupied(oe) => *oe.get(),
            Entry::Vacant(ve) => {
                let tyty = ty::Type::from_raw(self.ty_arena.lock().unwrap().alloc(value));
                ve.insert(tyty);
                tyty
            }
        }
    }

    pub fn alloc_struct_type(&self, value: ty::StructTypeValue) -> ty::StructType {
        ty::StructType::from_raw(self.struct_arena.lock().unwrap().alloc(value))
    }
}
