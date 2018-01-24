use libc;
use llvm::core::*;
use llvm::prelude::*;
use ty;

pub fn c_str(b: &[u8]) -> *const libc::c_char {
    b.as_ptr() as *const _
}

pub fn pointer_ty(sub_ty: LLVMTypeRef) -> LLVMTypeRef {
    unsafe { LLVMPointerType(sub_ty, 0) }
}

pub fn function_ty(
    ret_ty: LLVMTypeRef,
    mut param_types: Vec<LLVMTypeRef>,
    is_vararg: bool,
) -> LLVMTypeRef {
    unsafe {
        LLVMFunctionType(
            ret_ty,
            param_types.as_mut_ptr(),
            param_types.len() as _,
            is_vararg as _,
        )
    }
}

pub fn get_func_param(func: LLVMValueRef, index: usize) -> LLVMValueRef {
    unsafe { LLVMGetParam(func, index as _) }
}

pub fn remove_bb_from_parent(bb: LLVMBasicBlockRef) {
    unsafe {
        LLVMRemoveBasicBlockFromParent(bb);
    }
}

pub fn const_int(ty: LLVMTypeRef, c: i64, sign_ext: bool) -> LLVMValueRef {
    unsafe { LLVMConstInt(ty, c as _, sign_ext as _) }
}

pub fn const_real(ty: LLVMTypeRef, r: f64) -> LLVMValueRef {
    unsafe { LLVMConstReal(ty, r as _) }
}

pub fn ty_to_string(ty: &ty::Type) -> String {
    match *ty {
        ty::Type::Int => "int".to_string(),
        ty::Type::Double => "double".to_string(),
        ty::Type::Boolean => "boolean".to_string(),
        ty::Type::String => "string".to_string(),
        ty::Type::Void => "void".to_string(),
        ty::Type::LValue(ref sub) => format!("lvalue.{}", ty_to_string(sub)),
        ty::Type::Array(ref sub) => format!("array.{}", ty_to_string(sub)),
        _ => unimplemented!(),
    }
}
