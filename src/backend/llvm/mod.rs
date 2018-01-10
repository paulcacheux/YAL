use std;
use std::ffi::{CStr, CString};
use std::collections::HashMap;
use std::ptr;

use llvm;
use llvm::core::*;
use llvm::prelude::*;
use llvm::execution_engine::LLVMExecutionEngineRef;
use libc;

use ir;
use ty;
use interner::{InternerId, Interner};

mod helper;
use self::helper::*;

pub fn llvm_gen_program(program: ir::Program) -> Result<LLVMExecutionModule, CString> {
    let mut backend = Backend::new(program.strings);

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
pub struct Backend {
    context: Context,
    module: LLVMModuleRef,
    builder: IRBuilder,
    functions: HashMap<String, LLVMValueRef>,
    ids: HashMap<ir::IdentifierId, LLVMValueRef>,
    strings: Interner<String>,
    current_func: LLVMValueRef,
    current_break: LLVMBasicBlockRef,
    current_continue: LLVMBasicBlockRef,
}

impl Backend {
    pub fn new(strings: Interner<String>) -> Backend {
        let context = Context::new();
        let module = context.create_module(b"main\0");
        let builder = IRBuilder::new_in_context(&context);

        Backend {
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
        match *ty {
            ty::Type::Void => self.context.void_ty(),
            ty::Type::Int => self.context.i32_ty(),
            ty::Type::Double => self.context.double_ty(),
            ty::Type::Boolean => self.context.i1_ty(),
            ty::Type::String => Context::pointer_ty(self.context.i8_ty()),
            ty::Type::LValue(ref sub) => Context::pointer_ty(self.gen_type(sub)),
            _ => unimplemented!(),
        }
    }

    fn load_runtime(&mut self) {
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
                self.context.context,
                buf,
                &mut runtime_module,
                &mut err_msg,
            );

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
        let mut param_types: Vec<_> = function
            .parameters
            .iter()
            .map(|&(ref ty, _)| self.gen_type(ty))
            .collect();

        let func_ty = unsafe {
            LLVMFunctionType(ret_ty, param_types.as_mut_ptr(), param_types.len() as _, 0)
        };

        let c_name = CString::new(function.name.clone()).unwrap();

        unsafe {
            let func = LLVMAddFunction(self.module, c_name.as_ptr(), func_ty);
            self.functions.insert(function.name.clone(), func);
        }
    }

    fn gen_function(&mut self, function: ir::Function) {
        let func_ref = self.functions[&function.name];
        unsafe {
            let entry_bb =
                LLVMAppendBasicBlockInContext(self.context.context, func_ref, c_str(b"entry\0"));
            self.builder.position_at_end(entry_bb);
        }

        self.current_func = func_ref;

        for (index, (ty, id)) in function.parameters.into_iter().enumerate() {
            self.gen_parameter(&ty, id, func_ref, index);
        }

        if !self.gen_block_statement(function.body) {
            self.builder.build_unreachable();
        }
    }

    fn gen_parameter(
        &mut self,
        ty: &ty::Type,
        id: ir::IdentifierId,
        func: LLVMValueRef,
        index: usize,
    ) {
        let llvm_ty = self.gen_type(ty);
        let ptr = unsafe {
            let ptr = self.builder.build_alloca(llvm_ty, b"\0");
            let arg_value = LLVMGetParam(func, index as _);
            self.builder.build_store(arg_value, ptr);
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

    fn gen_statement(&mut self, statement: ir::Statement) -> bool {
        // return true if the statement end on a terminator
        match statement {
            ir::Statement::Block(block) => self.gen_block_statement(block),
            ir::Statement::VarDecl { ty, id } => self.gen_vardecl_statement(&ty, id),
            ir::Statement::If {
                condition,
                body,
                else_clause,
            } => self.gen_if(condition, body, else_clause),
            ir::Statement::While { condition, body } => self.gen_while(condition, body),
            ir::Statement::Return(expr) => self.gen_return_statement(expr),
            ir::Statement::Expression(expr) => {
                self.gen_expression(expr);
                false
            }
            ir::Statement::Break => self.gen_break_statement(),
            ir::Statement::Continue => self.gen_continue_statement(),
            _ => unimplemented!(),
        }
    }

    fn gen_vardecl_statement(&mut self, ty: &ty::Type, id: ir::IdentifierId) -> bool {
        let llvm_ty = self.gen_type(ty);
        let ptr = self.builder.build_alloca(llvm_ty, b"\0");

        self.ids.insert(id, ptr);
        false
    }

    fn gen_if(
        &mut self,
        cond: ir::TypedExpression,
        body: ir::BlockStatement,
        else_clause: ir::BlockStatement,
    ) -> bool {
        let cond = self.gen_expression(cond);
        unsafe {
            let then_bb = LLVMAppendBasicBlockInContext(
                self.context.context,
                self.current_func,
                c_str(b"then\0"),
            );
            let else_bb = LLVMAppendBasicBlockInContext(
                self.context.context,
                self.current_func,
                c_str(b"else\0"),
            );
            let end_bb = LLVMAppendBasicBlockInContext(
                self.context.context,
                self.current_func,
                c_str(b"end\0"),
            );

            self.builder.build_cond_br(cond, then_bb, else_bb);

            let mut then_res = true;
            let mut else_res = true;

            self.builder.position_at_end(then_bb);
            if !self.gen_block_statement(body) {
                self.builder.build_br(end_bb);
                then_res = false;
            }

            self.builder.position_at_end(else_bb);
            if !self.gen_block_statement(else_clause) {
                self.builder.build_br(end_bb);
                else_res = false;
            }

            let res = then_res && else_res;
            if res {
                LLVMRemoveBasicBlockFromParent(end_bb);
            } else {
                self.builder.position_at_end(end_bb);
            }
            res
        }
    }

    fn gen_while(&mut self, cond: ir::TypedExpression, body: ir::BlockStatement) -> bool {
        unsafe {
            let loop_bb = LLVMAppendBasicBlockInContext(
                self.context.context,
                self.current_func,
                c_str(b"loop\0"),
            );
            let then_bb = LLVMAppendBasicBlockInContext(
                self.context.context,
                self.current_func,
                c_str(b"then\0"),
            );
            let end_bb = LLVMAppendBasicBlockInContext(
                self.context.context,
                self.current_func,
                c_str(b"end\0"),
            );

            self.builder.build_br(loop_bb);
            self.builder.position_at_end(loop_bb);
            let cond = self.gen_expression(cond);
            self.builder.build_cond_br(cond, then_bb, end_bb);

            self.current_break = end_bb;
            self.current_continue = loop_bb;

            self.builder.position_at_end(then_bb);
            if self.gen_block_statement(body) {
                self.gen_next_bb();
            }
            self.builder.build_br(loop_bb);
            self.builder.position_at_end(end_bb);
        }
        false
    }

    fn gen_next_bb(&mut self) {
        unsafe {
            let bb = LLVMAppendBasicBlockInContext(
                self.context.context,
                self.current_func,
                c_str(b"next"),
            );
            self.builder.position_at_end(bb);
        }
    }

    fn gen_return_statement(&mut self, expr: Option<ir::TypedExpression>) -> bool {
        if let Some(expr) = expr {
            let expr = self.gen_expression(expr);
            self.builder.build_ret(expr);
        } else {
            self.builder.build_ret_void();
        }
        true
    }

    fn gen_break_statement(&mut self) -> bool {
        self.builder.build_br(self.current_break);
        true
    }

    fn gen_continue_statement(&mut self) -> bool {
        self.builder.build_br(self.current_continue);
        true
    }

    fn gen_expression(&mut self, expr: ir::TypedExpression) -> LLVMValueRef {
        let ir::TypedExpression { expr, .. } = expr;
        match expr {
            ir::Expression::Block(block) => self.gen_expr_block(*block),
            ir::Expression::LValueToRValue(sub) => self.gen_l2r_expr(*sub),
            ir::Expression::Literal(lit) => self.gen_literal(lit),
            ir::Expression::Identifier(id) => self.gen_identifier(id),
            ir::Expression::Assign { lhs, rhs } => self.gen_assign(*lhs, *rhs),
            ir::Expression::BinaryOperator { binop, lhs, rhs } => self.gen_binop(binop, *lhs, *rhs),
            ir::Expression::UnaryOperator { unop, sub } => self.gen_unop(unop, *sub),
            ir::Expression::Increment(sub) => self.gen_incdecrement(*sub, true),
            ir::Expression::Decrement(sub) => self.gen_incdecrement(*sub, false),
            ir::Expression::FunctionCall { function, args } => self.gen_funccall(&function, args),
            _ => unimplemented!(),
        }
    }

    fn gen_expr_block(&mut self, block: ir::BlockExpression) -> LLVMValueRef {
        for stmt in block.stmts {
            self.gen_statement(stmt);
        }
        self.gen_expression(block.final_expr)
    }

    fn gen_l2r_expr(&mut self, expr: ir::TypedExpression) -> LLVMValueRef {
        let expr = self.gen_expression(expr);
        self.builder.build_load(expr, b"\0")
    }

    fn gen_literal(&mut self, literal: ir::Literal) -> LLVMValueRef {
        unsafe {
            match literal {
                ir::Literal::IntLiteral(i) => {
                    let ty = self.gen_type(&ty::Type::Int);
                    LLVMConstInt(ty, i as _, 1)
                }
                ir::Literal::DoubleLiteral(d) => {
                    let ty = self.gen_type(&ty::Type::Double);
                    LLVMConstReal(ty, d as _)
                }
                ir::Literal::BooleanLiteral(b) => {
                    let ty = self.gen_type(&ty::Type::Boolean);
                    LLVMConstInt(ty, b as _, 0)
                }
                ir::Literal::StringLiteral(id) => self.gen_string_literal(id),
            }
        }
    }

    fn gen_string_literal(&mut self, id: InternerId) -> LLVMValueRef {
        let s = self.strings.get_ref(id);

        let gs = self.builder.build_global_string_ptr(s.to_string(), b"\0");
        let s_ty = self.gen_type(&ty::Type::String);
        self.builder.build_bitcast(gs, s_ty, b"\0")
    }

    fn gen_identifier(&mut self, id: ir::IdentifierId) -> LLVMValueRef {
        self.ids[&id]
    }

    fn gen_assign(&mut self, lhs: ir::TypedExpression, rhs: ir::TypedExpression) -> LLVMValueRef {
        let lhs = self.gen_expression(lhs);
        let rhs = self.gen_expression(rhs);

        self.builder.build_store(rhs, lhs);

        rhs
    }

    fn gen_binop(
        &mut self,
        binop: ir::BinaryOperatorKind,
        lhs: ir::TypedExpression,
        rhs: ir::TypedExpression,
    ) -> LLVMValueRef {
        let lhs = self.gen_expression(lhs);
        let rhs = self.gen_expression(rhs);

        use ir::BinaryOperatorKind as bok;
        use llvm::LLVMIntPredicate::*;
        use llvm::LLVMRealPredicate::*;

        macro_rules! cmp_builder {
            (@inner $pred:expr, $func:ident) => {
                {
                    fn tmp(b: &IRBuilder,
                        l: LLVMValueRef,
                        r: LLVMValueRef,
                        n: &[u8]) -> LLVMValueRef {
                        b.$func($pred, l, r, n)
                    }
                    tmp
                }
            };
            (@i $pred:expr) => {
                cmp_builder!(@inner $pred, build_icmp)
            };
            (@f $pred:expr) => {
                cmp_builder!(@inner $pred, build_fcmp)
            };
        }

        let func = match binop {
            bok::IntPlus => IRBuilder::build_add,
            bok::DoublePlus => IRBuilder::build_fadd,
            bok::IntMinus => IRBuilder::build_sub,
            bok::DoubleMinus => IRBuilder::build_fsub,
            bok::IntMultiply => IRBuilder::build_mul,
            bok::DoubleMultiply => IRBuilder::build_fmul,
            bok::IntDivide => IRBuilder::build_sdiv,
            bok::DoubleDivide => IRBuilder::build_fdiv,
            bok::IntModulo => IRBuilder::build_srem,
            bok::IntEqual => cmp_builder!(@i LLVMIntEQ),
            bok::DoubleEqual => cmp_builder!(@f LLVMRealUEQ),
            bok::BooleanEqual => cmp_builder!(@i LLVMIntEQ),
            bok::IntNotEqual => cmp_builder!(@i LLVMIntNE),
            bok::DoubleNotEqual => cmp_builder!(@f LLVMRealUNE),
            bok::BooleanNotEqual => cmp_builder!(@i LLVMIntNE),
            bok::IntLess => cmp_builder!(@i LLVMIntSLT),
            bok::DoubleLess => cmp_builder!(@f LLVMRealULT),
            bok::IntLessEqual => cmp_builder!(@i LLVMIntSLE),
            bok::DoubleLessEqual => cmp_builder!(@f LLVMRealULE),
            bok::IntGreater => cmp_builder!(@i LLVMIntSGT),
            bok::DoubleGreater => cmp_builder!(@f LLVMRealUGT),
            bok::IntGreaterEqual => cmp_builder!(@i LLVMIntSGE),
            bok::DoubleGreaterEqual => cmp_builder!(@f LLVMRealUGE),
        };

        func(&self.builder, lhs, rhs, b"\0")
    }

    fn gen_unop(&mut self, unop: ir::UnaryOperatorKind, sub: ir::TypedExpression) -> LLVMValueRef {
        let sub = self.gen_expression(sub);

        unsafe {
            match unop {
                ir::UnaryOperatorKind::IntMinus => {
                    let const0 = LLVMConstInt(self.gen_type(&ty::Type::Int), 0, 0);
                    self.builder.build_sub(const0, sub, b"\0")
                }
                ir::UnaryOperatorKind::DoubleMinus => {
                    let const0 = LLVMConstReal(self.gen_type(&ty::Type::Double), 0.0);
                    self.builder.build_fsub(const0, sub, b"\0")
                }
                ir::UnaryOperatorKind::BooleanNot => self.builder.build_not(sub, b"\0"),
            }
        }
    }

    fn gen_incdecrement(&mut self, sub: ir::TypedExpression, inc: bool) -> LLVMValueRef {
        let ptr = self.gen_expression(sub);

        let c1 = unsafe {
            let ty = self.gen_type(&ty::Type::Int);
            LLVMConstInt(ty, 1, 1)
        };

        let value = self.builder.build_load(ptr, b"\0");
        let value = if inc {
            self.builder.build_add(value, c1, b"\0")
        } else {
            self.builder.build_sub(value, c1, b"\0")
        };

        self.builder.build_store(value, ptr);

        ptr
    }

    fn gen_funccall(&mut self, func: &str, args: Vec<ir::TypedExpression>) -> LLVMValueRef {
        let func = self.functions[func];
        let args: Vec<_> = args.into_iter().map(|e| self.gen_expression(e)).collect();

        self.builder.build_call(func, args, b"\0")
    }

    fn into_exec_module(self) -> Result<LLVMExecutionModule, CString> {
        LLVMExecutionModule::from_backend(self)
    }
}

pub struct LLVMExecutionModule {
    backend: Backend,
    exec_engine: LLVMExecutionEngineRef,
    main_func: LLVMValueRef,
}

impl LLVMExecutionModule {
    fn from_backend(backend: Backend) -> Result<Self, CString> {
        use llvm::execution_engine::LLVMMCJITCompilerOptions;

        let mut exec_engine: LLVMExecutionEngineRef = std::ptr::null_mut();
        unsafe {
            let mut error: *mut libc::c_char = std::ptr::null_mut();
            let mut options: LLVMMCJITCompilerOptions = std::mem::zeroed();
            let options_size = std::mem::size_of::<LLVMMCJITCompilerOptions>();
            llvm::execution_engine::LLVMInitializeMCJITCompilerOptions(&mut options, options_size);

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
                &mut error,
            ) != 0
            {
                return Err(CString::from_raw(error));
            }
        }

        let main_func = unsafe { LLVMGetNamedFunction(backend.module, c_str(b"main\0")) };

        Ok(LLVMExecutionModule {
            backend,
            exec_engine,
            main_func,
        })
    }

    pub fn verify_module(&self) {
        unsafe {
            use llvm::analysis::{LLVMVerifierFailureAction, LLVMVerifyModule};
            LLVMVerifyModule(
                self.backend.module,
                LLVMVerifierFailureAction::LLVMPrintMessageAction,
                ptr::null_mut(),
            );
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
                ptr::null_mut(),
            );
        }
    }
}
