use typed_arena::Arena;

use std::sync::Mutex;

use ty;

pub struct Context {
    ty_arena: Mutex<Arena<ty::TypeValue>>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            ty_arena: Mutex::new(Arena::new()),
        }
    }

    pub fn alloc_type(&self, value: ty::TypeValue) -> ty::Type {
        ty::Type::from_raw(self.ty_arena.lock().unwrap().alloc(value))
    }
}
