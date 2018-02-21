use std::ops::Drop;
use std::ffi::{CStr, CString};

use llvm;
use llvm::core::*;
use llvm::prelude::*;

use backend::utils;
use self::utils::c_str;

#[derive(Debug, Clone)]
pub struct Context {
    pub context: LLVMContextRef,
}

impl Context {
    pub fn new() -> Context {
        let context = unsafe { LLVMContextCreate() };
        Context { context }
    }

    pub fn void_ty(&self) -> LLVMTypeRef {
        unsafe { LLVMVoidTypeInContext(self.context) }
    }

    pub fn i1_ty(&self) -> LLVMTypeRef {
        unsafe { LLVMInt1TypeInContext(self.context) }
    }

    pub fn i8_ty(&self) -> LLVMTypeRef {
        unsafe { LLVMInt8TypeInContext(self.context) }
    }

    pub fn i32_ty(&self) -> LLVMTypeRef {
        unsafe { LLVMInt32TypeInContext(self.context) }
    }

    pub fn i64_ty(&self) -> LLVMTypeRef {
        unsafe { LLVMInt64TypeInContext(self.context) }
    }

    pub fn double_ty(&self) -> LLVMTypeRef {
        unsafe { LLVMDoubleTypeInContext(self.context) }
    }

    pub fn raw_array_ty(&self, sub: LLVMTypeRef, index: LLVMTypeRef) -> LLVMTypeRef {
        let mut fields = [utils::pointer_ty(sub), index];
        unsafe { LLVMStructTypeInContext(self.context, fields.as_mut_ptr(), 2, 0 as _) }
    }

    pub fn array_ty(&self, sub: LLVMTypeRef, index: LLVMTypeRef) -> LLVMTypeRef {
        let raw_array = self.raw_array_ty(sub, index);
        utils::pointer_ty(raw_array)
    }

    pub fn create_struct_named(&self, name: &[u8]) -> LLVMTypeRef {
        unsafe { LLVMStructCreateNamed(self.context, c_str(name)) }
    }

    pub fn append_bb_to_func(&self, func: LLVMValueRef, name: &[u8]) -> LLVMBasicBlockRef {
        unsafe { LLVMAppendBasicBlockInContext(self.context, func, c_str(name)) }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { LLVMContextDispose(self.context) };
    }
}

#[derive(Debug, Clone)]
pub struct Module {
    pub module: LLVMModuleRef,
}

impl Module {
    pub fn new_in_context(context: &Context, name: &[u8]) -> Module {
        Module {
            module: unsafe { LLVMModuleCreateWithNameInContext(c_str(name), context.context) },
        }
    }

    pub fn add_function(&self, name: &CStr, ty: LLVMTypeRef) -> LLVMValueRef {
        unsafe { LLVMAddFunction(self.module, name.as_ptr(), ty) }
    }

    pub fn get_named_function(&self, name: &CStr) -> LLVMValueRef {
        unsafe { LLVMGetNamedFunction(self.module, name.as_ptr()) }
    }

    /* currently unused
    pub fn load_runtime(&self, context: &Context) {
        let mut bytes: Vec<_> = include_bytes!("./runtime.ll").as_ref().into();
        bytes.push(0);

        unsafe {
            let buf = LLVMCreateMemoryBufferWithMemoryRange(
                bytes.as_ptr() as *const _,
                (bytes.len() - 1) as _,
                c_str(b"\0"),
                1,
            );
            let mut runtime_module = ptr::null_mut();
            let mut err_msg = ptr::null_mut();

            let result = llvm::ir_reader::LLVMParseIRInContext(
                context.context,
                buf,
                &mut runtime_module,
                &mut err_msg,
            );

            if result != 0 {
                panic!("{}", CStr::from_ptr(err_msg).to_string_lossy().into_owned())
            }

            llvm::linker::LLVMLinkModules2(self.module, runtime_module);
        }
    }*/
}

#[derive(Debug, Clone)]
pub struct IRBuilder {
    pub builder: LLVMBuilderRef,
}

impl IRBuilder {
    pub fn new_in_context(context: &Context) -> IRBuilder {
        let builder = unsafe { LLVMCreateBuilderInContext(context.context) };

        IRBuilder { builder }
    }

    pub fn position_at_end(&self, bb: LLVMBasicBlockRef) {
        unsafe {
            LLVMPositionBuilderAtEnd(self.builder, bb);
        }
    }

    pub fn build_unreachable(&self) {
        unsafe {
            LLVMBuildUnreachable(self.builder);
        }
    }

    pub fn build_ret(&self, value: LLVMValueRef) {
        unsafe {
            LLVMBuildRet(self.builder, value);
        }
    }

    pub fn build_ret_void(&self) {
        unsafe {
            LLVMBuildRetVoid(self.builder);
        }
    }

    pub fn build_alloca(&self, ty: LLVMTypeRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildAlloca(self.builder, ty, c_str(name)) }
    }

    pub fn build_store(&self, value: LLVMValueRef, ptr: LLVMValueRef) {
        unsafe {
            LLVMBuildStore(self.builder, value, ptr);
        }
    }

    pub fn build_load(&self, ptr: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildLoad(self.builder, ptr, c_str(name)) }
    }

    pub fn build_cond_br(
        &self,
        cond: LLVMValueRef,
        true_bb: LLVMBasicBlockRef,
        false_bb: LLVMBasicBlockRef,
    ) {
        unsafe {
            LLVMBuildCondBr(self.builder, cond, true_bb, false_bb);
        }
    }

    pub fn build_br(&self, bb: LLVMBasicBlockRef) {
        unsafe {
            LLVMBuildBr(self.builder, bb);
        }
    }

    pub fn build_global_string_ptr(&self, s: String, name: &[u8]) -> LLVMValueRef {
        let cs = CString::new(s).unwrap();

        unsafe { LLVMBuildGlobalStringPtr(self.builder, cs.as_ptr(), c_str(name)) }
    }

    pub fn build_bitcast(&self, expr: LLVMValueRef, ty: LLVMTypeRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildBitCast(self.builder, expr, ty, c_str(name)) }
    }

    pub fn build_not(&self, expr: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildNot(self.builder, expr, c_str(name)) }
    }

    pub fn build_call(
        &self,
        func: LLVMValueRef,
        mut args: Vec<LLVMValueRef>,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe {
            LLVMBuildCall(
                self.builder,
                func,
                args.as_mut_ptr(),
                args.len() as _,
                c_str(name),
            )
        }
    }

    pub fn build_add(&self, lhs: LLVMValueRef, rhs: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildAdd(self.builder, lhs, rhs, c_str(name)) }
    }

    pub fn build_sub(&self, lhs: LLVMValueRef, rhs: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildSub(self.builder, lhs, rhs, c_str(name)) }
    }

    pub fn build_mul(&self, lhs: LLVMValueRef, rhs: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildMul(self.builder, lhs, rhs, c_str(name)) }
    }

    pub fn build_sdiv(&self, lhs: LLVMValueRef, rhs: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildSDiv(self.builder, lhs, rhs, c_str(name)) }
    }

    pub fn build_srem(&self, lhs: LLVMValueRef, rhs: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildSRem(self.builder, lhs, rhs, c_str(name)) }
    }

    pub fn build_fadd(&self, lhs: LLVMValueRef, rhs: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildFAdd(self.builder, lhs, rhs, c_str(name)) }
    }

    pub fn build_fsub(&self, lhs: LLVMValueRef, rhs: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildFSub(self.builder, lhs, rhs, c_str(name)) }
    }

    pub fn build_fmul(&self, lhs: LLVMValueRef, rhs: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildFMul(self.builder, lhs, rhs, c_str(name)) }
    }

    pub fn build_fdiv(&self, lhs: LLVMValueRef, rhs: LLVMValueRef, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildFDiv(self.builder, lhs, rhs, c_str(name)) }
    }

    pub fn build_icmp(
        &self,
        pred: llvm::LLVMIntPredicate,
        lhs: LLVMValueRef,
        rhs: LLVMValueRef,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe { LLVMBuildICmp(self.builder, pred, lhs, rhs, c_str(name)) }
    }

    pub fn build_fcmp(
        &self,
        pred: llvm::LLVMRealPredicate,
        lhs: LLVMValueRef,
        rhs: LLVMValueRef,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe { LLVMBuildFCmp(self.builder, pred, lhs, rhs, c_str(name)) }
    }

    pub fn build_zext(
        &self,
        value: LLVMValueRef,
        dest_ty: LLVMTypeRef,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe { LLVMBuildZExt(self.builder, value, dest_ty, c_str(name)) }
    }

    pub fn build_si_to_fp(
        &self,
        value: LLVMValueRef,
        dest_ty: LLVMTypeRef,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe { LLVMBuildSIToFP(self.builder, value, dest_ty, c_str(name)) }
    }

    pub fn build_fp_to_si(
        &self,
        value: LLVMValueRef,
        dest_ty: LLVMTypeRef,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe { LLVMBuildFPToSI(self.builder, value, dest_ty, c_str(name)) }
    }

    pub fn build_trunc(
        &self,
        value: LLVMValueRef,
        dest_ty: LLVMTypeRef,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe { LLVMBuildTrunc(self.builder, value, dest_ty, c_str(name)) }
    }

    pub fn build_gep(
        &self,
        ptr: LLVMValueRef,
        mut indices: Vec<LLVMValueRef>,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe {
            LLVMBuildGEP(
                self.builder,
                ptr,
                indices.as_mut_ptr(),
                indices.len() as _,
                c_str(name),
            )
        }
    }

    pub fn build_struct_gep(&self, ptr: LLVMValueRef, index: usize, name: &[u8]) -> LLVMValueRef {
        unsafe { LLVMBuildStructGEP(self.builder, ptr, index as _, c_str(name)) }
    }

    pub fn build_ptr_to_int(
        &self,
        ptr: LLVMValueRef,
        int_ty: LLVMTypeRef,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe { LLVMBuildPtrToInt(self.builder, ptr, int_ty, c_str(name)) }
    }

    pub fn build_int_to_ptr(
        &self,
        value: LLVMValueRef,
        dest_ty: LLVMTypeRef,
        name: &[u8],
    ) -> LLVMValueRef {
        unsafe { LLVMBuildIntToPtr(self.builder, value, dest_ty, c_str(name)) }
    }
}
