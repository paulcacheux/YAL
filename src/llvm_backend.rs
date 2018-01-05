use std;
use std::ops::Drop;
use std::ffi::{CString, CStr};
use std::collections::HashMap;
use std::ptr;

use llvm;
use llvm::core::*;
use llvm::prelude::*;
use llvm::execution_engine::LLVMExecutionEngineRef;
use libc;

use ir;
use ty;
use string_interner::{StringId, StringInterner};

pub fn llvm_gen_program(program: ir::Program) -> Result<LLVMExecutionModule, CString> {
    let mut backend = LLVMBackend::new(program.strings);

    //self.register_builtins();
    backend.load_runtime();

    for function in &program.declarations {
        backend.pre_gen_function(function);
    }

    for function in program.declarations {
        backend.gen_function(function);
    }

    backend.into_exec_module()
}

#[derive(Debug, Clone)]
pub struct LLVMBackend {
    context: LLVMContextRef,
    module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    functions: HashMap<String, LLVMValueRef>,
    ids: HashMap<ir::IdentifierId, LLVMValueRef>,
    strings: StringInterner,
    current_func: LLVMValueRef,
    current_break: LLVMBasicBlockRef,
    current_continue: LLVMBasicBlockRef,
}

fn c_str(b: &[u8]) -> *const libc::c_char {
    b.as_ptr() as *const _
}

impl LLVMBackend {
    pub fn new(strings: StringInterner) -> LLVMBackend {
        let context = unsafe { LLVMContextCreate() };
        let module = unsafe {
            LLVMModuleCreateWithNameInContext(c_str(b"main\0"), context)
        };
        let builder = unsafe { LLVMCreateBuilder() };

        LLVMBackend {
            context,
            module,
            builder,
            functions: HashMap::new(),
            ids: HashMap::new(),
            strings,
            current_func: ptr::null_mut(),
            current_break: ptr::null_mut(),
            current_continue: ptr::null_mut(),
        }
    }

    fn gen_type(&self, ty: &ty::Type) -> LLVMTypeRef {
        unsafe {
            match *ty {
                ty::Type::Void => LLVMVoidTypeInContext(self.context),
                ty::Type::Int => LLVMInt32TypeInContext(self.context),
                ty::Type::Double => LLVMDoubleTypeInContext(self.context),
                ty::Type::Boolean => LLVMInt1TypeInContext(self.context),
                ty::Type::String => {
                    LLVMPointerType(LLVMInt8TypeInContext(self.context), 0)
                },
                ty::Type::LValue(ref sub) => {
                    LLVMPointerType(self.gen_type(sub), 0)
                },
                ty::Type::Array(ref sub) => {
                    LLVMPointerType(self.gen_type(sub), 0)
                },
                _ => unimplemented!()
            }
        }
    }

    fn load_runtime(&mut self) {
        let mut bytes: Vec<_> = include_bytes!("../runtime/runtime.ll").as_ref().into();
        bytes.push(0);

        unsafe {
            let buf = LLVMCreateMemoryBufferWithMemoryRange(bytes.as_ptr() as *const _, (bytes.len() - 1) as _, c_str(b"\0"), 1);
            let mut runtime_module = ptr::null_mut();
            let mut err_msg = ptr::null_mut();

            let result = llvm::ir_reader::LLVMParseIRInContext(self.context, buf, &mut runtime_module, &mut err_msg);

            if result != 0 {
                panic!("{}", CStr::from_ptr(err_msg).to_string_lossy().into_owned())
            }

            llvm::linker::LLVMLinkModules2(self.module, runtime_module);
        }

        self.register_named_func("printInt".to_string());
        self.register_named_func("printDouble".to_string());
        self.register_named_func("printString".to_string());
        self.register_named_func("readInt".to_string());
        self.register_named_func("readDouble".to_string());

    }

    fn register_named_func(&mut self, name: String) {
        let c_name = CString::new(name.clone()).unwrap();
        let func = unsafe { LLVMGetNamedFunction(self.module, c_name.as_ptr()) };
        self.functions.insert(name, func);
    }

    fn pre_gen_function(&mut self, function: &ir::Function) {
        let ret_ty = self.gen_type(&function.return_ty);
        let mut param_types: Vec<_> = function.parameters.iter().map(|&(ref ty, _)| {
            self.gen_type(ty)
        }).collect();

        let func_ty = unsafe {
            LLVMFunctionType(ret_ty, param_types.as_mut_ptr(), param_types.len() as _, 0)
        };

        let c_name = CString::new(function.name.clone()).unwrap();

        unsafe {
            let func = LLVMAddFunction(self.module, c_name.as_ptr(),func_ty);
            self.functions.insert(function.name.clone(), func);
        }
    }

    fn gen_function(&mut self, function: ir::Function) {
        let func_ref = *self.functions.get(&function.name).unwrap();
        unsafe {
            let entry_bb = LLVMAppendBasicBlockInContext(
                self.context,
                func_ref,
                c_str(b"entry\0")
            );
            LLVMPositionBuilderAtEnd(self.builder, entry_bb);
        }

        self.current_func = func_ref;

        for (index, (ty, id)) in function.parameters.into_iter().enumerate() {
            self.gen_parameter(ty, id, func_ref, index);
        }

        if !self.gen_block_statement(function.body) {
            unsafe {
                LLVMBuildUnreachable(self.builder);
            }
        }
    }

    fn gen_parameter(&mut self, ty: ty::Type, id: ir::IdentifierId, func: LLVMValueRef, index: usize) {
        let llvm_ty = self.gen_type(&ty);
        let ptr = unsafe {
            let ptr = LLVMBuildAlloca(self.builder, llvm_ty, c_str(b"\0"));
            let arg_value = LLVMGetParam(func, index as _);
            LLVMBuildStore(self.builder, arg_value, ptr);
            ptr
        };

        self.ids.insert(id, ptr);
    }

    fn gen_block_statement(&mut self, block: ir::BlockStatement) -> bool {
        let mut res = false;
        for statement in block {
            res = self.gen_statement(statement);
        }
        res
    }

    fn gen_statement(&mut self, statement: ir::Statement) -> bool { // return true if the statement end on a terminator
        match statement {
            ir::Statement::Block(block) => self.gen_block_statement(block),
            ir::Statement::VarDecl { ty, id } => self.gen_vardecl_statement(ty, id),
            ir::Statement::If { condition, body, else_clause } => self.gen_if(condition, body, else_clause),
            ir::Statement::While { condition, body } => self.gen_while(condition, body),
            ir::Statement::Return(expr) => self.gen_return_statement(expr),
            ir::Statement::Expression(expr) => { self.gen_expression(expr); false },
            ir::Statement::Break => self.gen_break_statement(),
            ir::Statement::Continue => self.gen_continue_statement(),
            _ => unimplemented!()
        }
    }

    fn gen_vardecl_statement(&mut self, ty: ty::Type, id: ir::IdentifierId) -> bool {
        let llvm_ty = self.gen_type(&ty);
        let ptr = unsafe {
            LLVMBuildAlloca(self.builder, llvm_ty, c_str(b"\0"))
        };

        self.ids.insert(id, ptr);
        false
    }

    fn gen_if(&mut self, cond: ir::TypedExpression, body: ir::BlockStatement, else_clause: ir::BlockStatement) -> bool {
        let cond = self.gen_expression(cond);
        unsafe {
            let then_bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"then\0"));
            let else_bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"else\0"));
            let end_bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"end\0"));

            LLVMBuildCondBr(self.builder, cond, then_bb, else_bb);

            let mut then_res = true;
            let mut else_res = true;

            LLVMPositionBuilderAtEnd(self.builder, then_bb);
            if !self.gen_block_statement(body) {
                LLVMBuildBr(self.builder, end_bb);
                then_res = false;
            }
            
            LLVMPositionBuilderAtEnd(self.builder, else_bb);
            if !self.gen_block_statement(else_clause) {
                LLVMBuildBr(self.builder, end_bb);
                else_res = false;
            }

            let res = then_res && else_res;
            if res {
                LLVMRemoveBasicBlockFromParent(end_bb);
            } else {
                LLVMPositionBuilderAtEnd(self.builder, end_bb);
            }
            res
        }
    }

    fn gen_while(&mut self, cond: ir::TypedExpression, body: ir::BlockStatement) -> bool {
        unsafe {
            let loop_bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"loop\0"));
            let then_bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"then\0"));
            let end_bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"end\0"));

            LLVMBuildBr(self.builder, loop_bb);
            LLVMPositionBuilderAtEnd(self.builder, loop_bb);
            let cond = self.gen_expression(cond);
            LLVMBuildCondBr(self.builder, cond, then_bb, end_bb);

            self.current_break = end_bb;
            self.current_continue = loop_bb;

            LLVMPositionBuilderAtEnd(self.builder, then_bb);
            if self.gen_block_statement(body) {
                self.gen_next_bb();
            }
            LLVMBuildBr(self.builder, loop_bb);
            LLVMPositionBuilderAtEnd(self.builder, end_bb);
            
        }
        false
    }

    fn gen_next_bb(&mut self) {
        unsafe {
            let bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"next"));
            LLVMPositionBuilderAtEnd(self.builder, bb);
        }
    }
    
    fn gen_return_statement(&mut self, expr: Option<ir::TypedExpression>) -> bool {
        if let Some(expr) = expr {
            let expr = self.gen_expression(expr);
            unsafe {
                LLVMBuildRet(self.builder, expr);
            }
        } else {
            unsafe {
                LLVMBuildRetVoid(self.builder);
            }
        }
        true
    }

    fn gen_break_statement(&mut self) -> bool {
        unsafe {
            LLVMBuildBr(self.builder, self.current_break);
        }
        true
    }

    fn gen_continue_statement(&mut self) -> bool {
        unsafe {
            LLVMBuildBr(self.builder, self.current_continue);
        }
        true
    }

    fn gen_expression(&mut self, expr: ir::TypedExpression) -> LLVMValueRef {
        let ir::TypedExpression{ expr, .. } = expr;
        match expr {
            ir::Expression::LValueToRValue(sub) => self.gen_l2r_expr(*sub),
            ir::Expression::Literal(lit) => self.gen_literal(lit),
            ir::Expression::Identifier(id) => self.gen_identifier(id),
            ir::Expression::Assign { lhs, rhs } => self.gen_assign(*lhs, *rhs),
            ir::Expression::BinaryOperator { binop, lhs, rhs } => self.gen_binop(binop, *lhs, *rhs),
            ir::Expression::LazyOperator { lazyop, lhs, rhs } => self.gen_lazyop(lazyop, *lhs, *rhs),
            ir::Expression::UnaryOperator { unop, sub } => self.gen_unop(unop, *sub),
            ir::Expression::Increment(sub) => self.gen_incdecrement(*sub, true),
            ir::Expression::Decrement(sub) => self.gen_incdecrement(*sub, false),
            ir::Expression::FunctionCall { function, args } => self.gen_funccall(function, args),
            _ => unimplemented!(),
        }
    }

    fn gen_l2r_expr(&mut self, expr: ir::TypedExpression) -> LLVMValueRef {
        let expr = self.gen_expression(expr);
        unsafe {
            LLVMBuildLoad(self.builder, expr, c_str(b"\0"))
        }
    }

    fn gen_literal(&mut self, literal: ir::Literal) -> LLVMValueRef {
        unsafe {
            match literal {
                ir::Literal::IntLiteral(i) => {
                    let ty = self.gen_type(&ty::Type::Int);
                    LLVMConstInt(ty, i as _, 1)
                },
                ir::Literal::DoubleLiteral(d) => {
                    let ty = self.gen_type(&ty::Type::Double);
                    LLVMConstReal(ty, d as _)
                },
                ir::Literal::BooleanLiteral(b) => {
                    let ty = self.gen_type(&ty::Type::Boolean);
                    LLVMConstInt(ty, b as _, 0)
                },
                ir::Literal::StringLiteral(id) => {
                    self.gen_string_literal(id)
                }
            }     
        }
    }

    fn gen_string_literal(&mut self, id: StringId) -> LLVMValueRef {
        let s = self.strings.get_str(id);
        let cs = CString::new(s.to_string()).unwrap();

        unsafe {
            let gs = LLVMBuildGlobalStringPtr(self.builder, cs.as_ptr(), c_str(b"\0"));
            let s_ty = self.gen_type(&ty::Type::String);
            
            LLVMBuildBitCast(self.builder, gs, s_ty, c_str(b"\0"))
        }
    }

    fn gen_identifier(&mut self, id: ir::IdentifierId) -> LLVMValueRef {
        *self.ids.get(&id).unwrap()
    }

    fn gen_assign(&mut self, lhs: ir::TypedExpression, rhs: ir::TypedExpression) -> LLVMValueRef {
        let lhs = self.gen_expression(lhs);
        let rhs = self.gen_expression(rhs);
        
        unsafe {
            LLVMBuildStore(self.builder, rhs, lhs);
        }

        rhs
    }

    fn gen_binop(&mut self, binop: ir::BinaryOperatorKind, lhs: ir::TypedExpression, rhs: ir::TypedExpression) -> LLVMValueRef {
        let lhs = self.gen_expression(lhs);
        let rhs = self.gen_expression(rhs);

        let name = c_str(b"\0");
        let b = self.builder;

        use ir::BinaryOperatorKind as bok;
        use llvm::LLVMIntPredicate::*;
        use llvm::LLVMRealPredicate::*;
        unsafe {
            match binop {
                bok::IntPlus => LLVMBuildAdd(b, lhs, rhs, name),
                bok::DoublePlus => LLVMBuildFAdd(b, lhs, rhs, name),
                bok::IntMinus => LLVMBuildSub(b, lhs, rhs, name),
                bok::DoubleMinus => LLVMBuildFSub(b, lhs, rhs, name),
                bok::IntMultiply => LLVMBuildMul(b, lhs, rhs, name),
                bok::DoubleMultiply => LLVMBuildFMul(b, lhs, rhs, name),
                bok::IntDivide => LLVMBuildSDiv(b, lhs, rhs, name),
                bok::DoubleDivide => LLVMBuildFDiv(b, lhs, rhs, name),
                bok::IntModulo => LLVMBuildSRem(b, lhs, rhs, name),
                bok::IntEqual => LLVMBuildICmp(b, LLVMIntEQ, lhs, rhs, name),
                bok::DoubleEqual => LLVMBuildFCmp(b, LLVMRealUEQ, lhs, rhs, name),
                bok::BooleanEqual => LLVMBuildICmp(b, LLVMIntEQ, lhs, rhs, name),
                bok::IntNotEqual => LLVMBuildICmp(b, LLVMIntNE, lhs, rhs, name),
                bok::DoubleNotEqual => LLVMBuildFCmp(b, LLVMRealUNE, lhs, rhs, name),
                bok::BooleanNotEqual => LLVMBuildICmp(b, LLVMIntNE, lhs, rhs, name),
                bok::IntLess => LLVMBuildICmp(b, LLVMIntSLT, lhs, rhs, name),
                bok::DoubleLess => LLVMBuildFCmp(b, LLVMRealULT, lhs, rhs, name),
                bok::IntLessEqual => LLVMBuildICmp(b, LLVMIntSLE, lhs, rhs, name),
                bok::DoubleLessEqual => LLVMBuildFCmp(b, LLVMRealULE, lhs, rhs, name),
                bok::IntGreater => LLVMBuildICmp(b, LLVMIntSGT, lhs, rhs, name),
                bok::DoubleGreater => LLVMBuildFCmp(b, LLVMRealUGT, lhs, rhs, name),
                bok::IntGreaterEqual => LLVMBuildICmp(b, LLVMIntSGE, lhs, rhs, name),
                bok::DoubleGreaterEqual => LLVMBuildFCmp(b, LLVMRealUGE, lhs, rhs, name),
            }
        }
    }

    fn gen_lazyop(&mut self, lazyop: ir::LazyOperatorKind, lhs: ir::TypedExpression, rhs: ir::TypedExpression) -> LLVMValueRef {
        let lhs = self.gen_expression(lhs);
        let bool_ty = self.gen_type(&ty::Type::Boolean);
        unsafe {
            let (condition, then_value) = match lazyop {
                ir::LazyOperatorKind::BooleanLogicalAnd => {
                    let condition = LLVMBuildNot(self.builder, lhs, c_str(b"\0"));
                    let then_value = LLVMConstInt(bool_ty, 0, 0);
                    (condition, then_value)
                },
                ir::LazyOperatorKind::BooleanLogicalOr => {
                    let then_value = LLVMConstInt(bool_ty, 1, 1);
                    (lhs, then_value)
                }
            };

            let then_bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"then\0"));
            let else_bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"else\0"));
            let end_bb = LLVMAppendBasicBlockInContext(self.context, self.current_func, c_str(b"end\0"));

            LLVMBuildCondBr(self.builder, condition, then_bb, else_bb);

            LLVMPositionBuilderAtEnd(self.builder, then_bb);
            LLVMBuildBr(self.builder, end_bb);
            LLVMPositionBuilderAtEnd(self.builder, else_bb);
            let else_value = self.gen_expression(rhs);
            let else_out_bb = LLVMGetInsertBlock(self.builder);
            LLVMBuildBr(self.builder, end_bb);

            let mut values = [then_value, else_value];
            let mut bbs = [then_bb, else_out_bb];

            LLVMPositionBuilderAtEnd(self.builder, end_bb);
            let phi = LLVMBuildPhi(self.builder, bool_ty, c_str(b"\0"));
            LLVMAddIncoming(phi, values.as_mut_ptr(), bbs.as_mut_ptr(), 2);
            phi
        }
    }

    fn gen_unop(&mut self, unop: ir::UnaryOperatorKind, sub: ir::TypedExpression) -> LLVMValueRef {
        let sub = self.gen_expression(sub);
        let name = c_str(b"\0");

        unsafe {
            match unop {
                ir::UnaryOperatorKind::IntMinus => {
                    let const0 = LLVMConstInt(self.gen_type(&ty::Type::Int), 0, 0);
                    LLVMBuildSub(self.builder, const0, sub, name)
                },
                ir::UnaryOperatorKind::DoubleMinus => {
                    let const0 = LLVMConstReal(self.gen_type(&ty::Type::Double), 0.0);
                    LLVMBuildFSub(self.builder, const0, sub, name)
                },
                ir::UnaryOperatorKind::BooleanNot => {
                    LLVMBuildNot(self.builder, sub, name)
                }
            }
        }
    }

    fn gen_incdecrement(&mut self, sub: ir::TypedExpression, inc: bool) -> LLVMValueRef {
        let ptr = self.gen_expression(sub);
        let name = c_str(b"\0");

        unsafe {
            let ty = self.gen_type(&ty::Type::Int);
            let c1 = LLVMConstInt(ty, 1, 1);

            let value = LLVMBuildLoad(self.builder, ptr, c_str(b"\0"));
            let value = if inc {
                LLVMBuildAdd(self.builder, value, c1, name)
            } else {
                LLVMBuildSub(self.builder, value, c1, name)
            };

            LLVMBuildStore(self.builder, value, ptr);
        }
        ptr
    }

    fn gen_funccall(&mut self, func: String, args: Vec<ir::TypedExpression>) -> LLVMValueRef {
        let func = *self.functions.get(&func).unwrap();

        let mut args: Vec<_> = args.into_iter().map(|e| self.gen_expression(e)).collect();

        unsafe {
            LLVMBuildCall(self.builder, func, args.as_mut_ptr(), args.len() as _, c_str(b"\0"))
        }
    }

    fn into_exec_module(self) -> Result<LLVMExecutionModule, CString> {
        LLVMExecutionModule::from_backend(self)
    }
}

impl Drop for LLVMBackend {
    fn drop(&mut self) {
        unsafe {
            LLVMContextDispose(self.context)
        };
    }
}

pub struct LLVMExecutionModule {
    backend: LLVMBackend,
    exec_engine: LLVMExecutionEngineRef,
    main_func: LLVMValueRef
}

impl LLVMExecutionModule {
    fn from_backend(backend: LLVMBackend) -> Result<Self, CString> {
        use llvm::execution_engine::LLVMMCJITCompilerOptions;
        
        let mut exec_engine: LLVMExecutionEngineRef = std::ptr::null_mut();
        unsafe {
            let mut error: *mut libc::c_char = std::ptr::null_mut();
            let mut options: LLVMMCJITCompilerOptions = std::mem::zeroed();
            let options_size = 
                std::mem::size_of::<LLVMMCJITCompilerOptions>();
            llvm::execution_engine::LLVMInitializeMCJITCompilerOptions(
                &mut options,
                options_size
            );

            options.OptLevel = 3;

            llvm::target::LLVM_InitializeNativeTarget();
            llvm::target::LLVM_InitializeNativeAsmPrinter();
            llvm::target::LLVM_InitializeNativeAsmParser();
            llvm::execution_engine::LLVMLinkInMCJIT();
            if llvm::execution_engine::LLVMCreateMCJITCompilerForModule(
                &mut exec_engine,
                backend.module,
                &mut options,
                options_size,
                &mut error
                ) != 0 {
                return Err(CString::from_raw(error));
            }
        }

        let main_func = unsafe {
            LLVMGetNamedFunction(backend.module, c_str(b"main\0"))
        };

        Ok(LLVMExecutionModule {
            backend,
            exec_engine,
            main_func
        })
    }

    pub fn verify_module(&self) {
        unsafe {
            use llvm::analysis::{LLVMVerifierFailureAction, LLVMVerifyModule};
            LLVMVerifyModule(self.backend.module, LLVMVerifierFailureAction::LLVMPrintMessageAction, ptr::null_mut());
        }
    }

    pub fn print_module(&self) {
        unsafe {
            LLVMDumpModule(self.backend.module);
        }
    }

    pub fn optimize(&mut self) {
        unsafe {
            let pass = LLVMCreatePassManager();
            llvm::transforms::scalar::LLVMAddConstantPropagationPass(pass);
            llvm::transforms::scalar::LLVMAddInstructionCombiningPass(pass);
            llvm::transforms::scalar::LLVMAddPromoteMemoryToRegisterPass(pass);
            llvm::transforms::scalar::LLVMAddGVNPass(pass);
            llvm::transforms::scalar::LLVMAddCFGSimplificationPass(pass);
            LLVMRunPassManager(pass, self.backend.module);
            LLVMDisposePassManager(pass);
        }
    }

    pub fn call_main(&self) {
        unsafe {
            llvm::execution_engine::LLVMRunFunction(
                self.exec_engine,
                self.main_func,
                0,
                ptr::null_mut()
            );
        }
    }
}
