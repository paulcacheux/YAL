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
use interner::{Interner, InternerId};

pub mod helper;
mod utils;
use self::utils::c_str;
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
    module: Module,
    builder: IRBuilder,
    functions: HashMap<String, LLVMValueRef>,
    ids: HashMap<ir::IdentifierId, LLVMValueRef>,
    new_arrays: HashMap<ty::Type, LLVMValueRef>,
    strings: Interner<String>,
    current_func: LLVMValueRef,
    current_break: LLVMBasicBlockRef,
    current_continue: LLVMBasicBlockRef,
}

impl Backend {
    pub fn new(strings: Interner<String>) -> Backend {
        let context = Context::new();
        let module = Module::new_in_context(&context, b"main\0");
        let builder = IRBuilder::new_in_context(&context);

        Backend {
            context,
            module,
            builder,
            functions: HashMap::new(),
            ids: HashMap::new(),
            new_arrays: HashMap::new(),
            strings,
            current_func: ptr::null_mut(),
            current_break: ptr::null_mut(),
            current_continue: ptr::null_mut(),
        }
    }

    fn gen_raw_array_type(&self, sub: &ty::Type) -> LLVMTypeRef {
        self.context
            .raw_array_ty(self.gen_type(sub), self.context.i32_ty())
    }

    fn gen_type(&self, ty: &ty::Type) -> LLVMTypeRef {
        match *ty {
            ty::Type::Void => self.context.void_ty(),
            ty::Type::Int => self.context.i32_ty(),
            ty::Type::Double => self.context.double_ty(),
            ty::Type::Boolean => self.context.i1_ty(),
            ty::Type::String => utils::pointer_ty(self.context.i8_ty()),
            ty::Type::LValue(ref sub) => utils::pointer_ty(self.gen_type(sub)),
            ty::Type::Array(ref sub) => self.context
                .array_ty(self.gen_type(sub), self.context.i32_ty()),
            _ => unimplemented!(),
        }
    }

    fn generate_new_array_func(&mut self, ty: &ty::Type) -> LLVMValueRef {
        let raw_array_llvm_ty = self.gen_raw_array_type(ty);
        let array_llvm_ty = utils::pointer_ty(raw_array_llvm_ty);
        let sub_llvm_ty = self.gen_type(ty);
        let func_ty = utils::function_ty(array_llvm_ty, vec![self.context.i32_ty()]);

        let func_name = format!("builtin.new_array.{}", utils::ty_to_string(ty));
        let c_name = CString::new(func_name).unwrap();

        let func_ref = self.module.add_function(&c_name, func_ty);
        let builder = IRBuilder::new_in_context(&self.context);
        let entry_bb = self.context.append_bb_to_func(func_ref, b"entry\0");
        builder.position_at_end(entry_bb);

        let size = builder.build_zext(
            utils::get_func_param(func_ref, 0),
            self.context.i64_ty(),
            b"\0",
        );

        let array_ptr = builder.build_malloc(raw_array_llvm_ty, b"\0");
        let sub_array_ptr = builder.build_array_malloc(sub_llvm_ty, size, b"\0");

        let ptr_field = builder.build_struct_gep(array_ptr, 0, b"\0");
        let size_field = builder.build_struct_gep(array_ptr, 1, b"\0");

        builder.build_store(sub_array_ptr, ptr_field);
        builder.build_store(utils::get_func_param(func_ref, 0), size_field);
        builder.build_ret(array_ptr);

        func_ref
    }

    fn get_new_array_func(&mut self, ty: &ty::Type) -> LLVMValueRef {
        if let Some(&value) = self.new_arrays.get(ty) {
            value
        } else {
            let new_func = self.generate_new_array_func(ty);
            self.new_arrays.insert(ty.clone(), new_func);
            new_func
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

            llvm::linker::LLVMLinkModules2(self.module.module, runtime_module);
        }

        self.register_named_func("printInt".to_string());
        self.register_named_func("printDouble".to_string());
        self.register_named_func("printString".to_string());
        self.register_named_func("readInt".to_string());
        self.register_named_func("readDouble".to_string());
        self.register_named_func("malloc".to_string());
    }

    fn register_named_func(&mut self, name: String) {
        let c_name = CString::new(name.clone()).unwrap();
        let func = self.module.get_named_function(&c_name);
        self.functions.insert(name, func);
    }

    fn pre_gen_function(&mut self, function: &ir::Function) {
        let ret_ty = self.gen_type(&function.return_ty);
        let param_types: Vec<_> = function
            .parameters
            .iter()
            .map(|&(ref ty, _)| self.gen_type(ty))
            .collect();

        let func_ty = utils::function_ty(ret_ty, param_types);
        let c_name = CString::new(function.name.clone()).unwrap();

        let func = self.module.add_function(&c_name, func_ty);
        self.functions.insert(function.name.clone(), func);
    }

    fn gen_function(&mut self, function: ir::Function) {
        let func_ref = self.functions[&function.name];
        let entry_bb = self.context.append_bb_to_func(func_ref, b"entry\0");
        self.builder.position_at_end(entry_bb);

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
        let ptr = self.builder.build_alloca(llvm_ty, b"\0");
        let arg_value = utils::get_func_param(func, index);
        self.builder.build_store(arg_value, ptr);
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
            ir::Statement::VarDecl { ty, id, init } => self.gen_vardecl_statement(&ty, id, init),
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
        }
    }

    fn gen_vardecl_statement(
        &mut self,
        ty: &ty::Type,
        id: ir::IdentifierId,
        init: Option<ir::TypedExpression>,
    ) -> bool {
        let llvm_ty = self.gen_type(ty);
        let ptr = self.builder.build_alloca(llvm_ty, b"\0");

        if let Some(init) = init {
            let init_value = self.gen_expression(init);
            self.builder.build_store(init_value, ptr);
        }

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
        let then_bb = self.context.append_bb_to_func(self.current_func, b"then\0");
        let else_bb = self.context.append_bb_to_func(self.current_func, b"else\0");
        let end_bb = self.context.append_bb_to_func(self.current_func, b"end\0");

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
            utils::remove_bb_from_parent(end_bb);
        } else {
            self.builder.position_at_end(end_bb);
        }
        res
    }

    fn gen_while(&mut self, cond: ir::TypedExpression, body: ir::BlockStatement) -> bool {
        let loop_bb = self.context.append_bb_to_func(self.current_func, b"loop\0");
        let then_bb = self.context.append_bb_to_func(self.current_func, b"then\0");
        let end_bb = self.context.append_bb_to_func(self.current_func, b"end\0");

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
        false
    }

    fn gen_next_bb(&mut self) {
        let bb = self.context.append_bb_to_func(self.current_func, b"next\0");
        self.builder.position_at_end(bb);
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
            ir::Expression::Subscript { array, index } => self.gen_subscript(*array, *index),
            ir::Expression::FunctionCall { function, args } => self.gen_funccall(&function, args),
            ir::Expression::NewArray { sub_ty, size } => self.gen_new_array(sub_ty, *size),
            ir::Expression::ArrayLength(sub) => self.gen_array_len(*sub),
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
        match literal {
            ir::Literal::IntLiteral(i) => {
                let ty = self.gen_type(&ty::Type::Int);
                utils::const_int(ty, i, true)
            }
            ir::Literal::DoubleLiteral(d) => {
                let ty = self.gen_type(&ty::Type::Double);
                utils::const_real(ty, d)
            }
            ir::Literal::BooleanLiteral(b) => {
                let ty = self.gen_type(&ty::Type::Boolean);
                utils::const_int(ty, b as _, false)
            }
            ir::Literal::StringLiteral(id) => self.gen_string_literal(id),
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

        match unop {
            ir::UnaryOperatorKind::IntMinus => {
                let const0 = utils::const_int(self.gen_type(&ty::Type::Int), 0, false);
                self.builder.build_sub(const0, sub, b"\0")
            }
            ir::UnaryOperatorKind::DoubleMinus => {
                let const0 = utils::const_real(self.gen_type(&ty::Type::Double), 0.0);
                self.builder.build_fsub(const0, sub, b"\0")
            }
            ir::UnaryOperatorKind::BooleanNot => self.builder.build_not(sub, b"\0"),
        }
    }

    fn gen_incdecrement(&mut self, sub: ir::TypedExpression, inc: bool) -> LLVMValueRef {
        let ptr = self.gen_expression(sub);

        let c1 = utils::const_int(self.gen_type(&ty::Type::Int), 1, true);

        let value = self.builder.build_load(ptr, b"\0");
        let value = if inc {
            self.builder.build_add(value, c1, b"\0")
        } else {
            self.builder.build_sub(value, c1, b"\0")
        };

        self.builder.build_store(value, ptr);

        ptr
    }

    fn gen_subscript(
        &mut self,
        array: ir::TypedExpression,
        index: ir::TypedExpression,
    ) -> LLVMValueRef {
        let array = self.gen_expression(array);
        let index = self.gen_expression(index);

        let ptr_ptr = self.builder.build_struct_gep(array, 0, b"\0");
        let ptr = self.builder.build_load(ptr_ptr, b"\0");
        self.builder.build_gep(ptr, vec![index], b"\0")
    }

    fn gen_funccall(&mut self, func: &str, args: Vec<ir::TypedExpression>) -> LLVMValueRef {
        let func = self.functions[func];
        let args: Vec<_> = args.into_iter().map(|e| self.gen_expression(e)).collect();

        self.builder.build_call(func, args, b"\0")
    }

    fn gen_new_array(&mut self, sub_ty: ty::Type, size: ir::TypedExpression) -> LLVMValueRef {
        let size = self.gen_expression(size);
        let na_func = self.get_new_array_func(&sub_ty);
        self.builder.build_call(na_func, vec![size], b"\0")
    }

    fn gen_array_len(&mut self, sub: ir::TypedExpression) -> LLVMValueRef {
        let array = self.gen_expression(sub);
        let size_ptr = self.builder.build_struct_gep(array, 1, b"\0");
        self.builder.build_load(size_ptr, b"\0")
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
                backend.module.module,
                &mut options,
                options_size,
                &mut error,
            ) != 0
            {
                return Err(CString::from_raw(error));
            }
        }

        let main_func = backend
            .module
            .get_named_function(&CString::new("main").unwrap());

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
                self.backend.module.module,
                LLVMVerifierFailureAction::LLVMPrintMessageAction,
                ptr::null_mut(),
            );
        }
    }

    pub fn print_module(&self) {
        unsafe {
            LLVMDumpModule(self.backend.module.module);
        }
    }

    pub fn optimize(&mut self) {
        use llvm::transforms::pass_manager_builder::*;
        unsafe {
            let builder = LLVMPassManagerBuilderCreate();
            LLVMPassManagerBuilderSetOptLevel(builder, 2 as _); // TODO make it configurable
            let pass_manager = LLVMCreatePassManager();
            LLVMPassManagerBuilderPopulateModulePassManager(builder, pass_manager);
            LLVMPassManagerBuilderDispose(builder);

            LLVMRunPassManager(pass_manager, self.backend.module.module);
            LLVMRunPassManager(pass_manager, self.backend.module.module);

            LLVMDisposePassManager(pass_manager);
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
