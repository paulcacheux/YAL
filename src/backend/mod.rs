use std::ffi::CString;
use std::collections::HashMap;
use std::ptr;

use llvm::prelude::*;

use ir;
use ty;
use common;
use interner::{Interner, InternerId};

mod helper;
pub mod execution_module;
mod utils;
use self::helper::*;
use self::execution_module::ExecutionModule;

pub fn llvm_codegen_program(program: ir::Program, strings: &Interner<String>) -> ExecutionModule {
    let mut backend = Backend::new(strings);

    for decl in &program.declarations {
        match *decl {
            ir::Declaration::ExternFunction(ref exfunc) => {
                backend.pre_codegen_extern_function(exfunc)
            }
            ir::Declaration::Function(ref func) => backend.pre_codegen_function(func),
        }
    }

    for decl in program.declarations {
        if let ir::Declaration::Function(function) = decl {
            backend.codegen_function(function);
        }
    }

    backend.into_exec_module()
}

#[derive(Debug, Clone)]
struct Backend<'s> {
    context: Context,
    module: Module,
    builder: IRBuilder,
    ids: HashMap<ir::IdentifierId, LLVMValueRef>,
    strings: &'s Interner<String>,
    current_func: LLVMValueRef,
    current_break: LLVMBasicBlockRef,
    current_continue: LLVMBasicBlockRef,
}

impl<'s> Backend<'s> {
    fn new(strings: &'s Interner<String>) -> Self {
        let context = Context::new();
        let module = Module::new_in_context(&context, b"main\0");
        let builder = IRBuilder::new_in_context(&context);

        Backend {
            context,
            module,
            builder,
            ids: HashMap::new(),
            strings,
            current_func: ptr::null_mut(),
            current_break: ptr::null_mut(),
            current_continue: ptr::null_mut(),
        }
    }

    fn codegen_type(&self, ty: &ty::Type) -> LLVMTypeRef {
        match *ty {
            ty::Type::Void => self.context.void_ty(),
            ty::Type::Int => self.context.i32_ty(),
            ty::Type::Double => self.context.double_ty(),
            ty::Type::Boolean => self.context.i1_ty(),
            ty::Type::String => utils::pointer_ty(self.context.i8_ty()),
            ty::Type::LValue(ref sub) => utils::pointer_ty(self.codegen_type(sub)),
            ty::Type::Pointer(ref sub) => utils::pointer_ty(self.codegen_type(sub)),
        }
    }

    fn pre_codegen_extern_function(&mut self, exfunc: &ir::ExternFunction) {
        let ret_ty = self.codegen_type(&exfunc.ty.return_ty);
        let param_types: Vec<_> = exfunc
            .ty
            .parameters_ty
            .iter()
            .map(|ty| self.codegen_type(ty))
            .collect();

        let func_ty = utils::function_ty(ret_ty, param_types, exfunc.ty.is_vararg);
        let c_name = CString::new(exfunc.name.clone()).unwrap();

        self.module.add_function(&c_name, func_ty);
    }

    fn pre_codegen_function(&mut self, function: &ir::Function) {
        let ret_ty = self.codegen_type(&function.return_ty);
        let param_types: Vec<_> = function
            .parameters
            .iter()
            .map(|&(ref ty, _)| self.codegen_type(ty))
            .collect();

        let func_ty = utils::function_ty(ret_ty, param_types, false);
        let c_name = CString::new(function.name.clone()).unwrap();

        self.module.add_function(&c_name, func_ty);
    }

    fn codegen_function(&mut self, function: ir::Function) {
        let func_ref = self.module
            .get_named_function(&CString::new(function.name).unwrap());
        let entry_bb = self.context.append_bb_to_func(func_ref, b"entry\0");
        self.builder.position_at_end(entry_bb);

        self.current_func = func_ref;

        for (index, (ty, id)) in function.parameters.into_iter().enumerate() {
            self.codegen_parameter(&ty, id, func_ref, index);
        }

        for decl in function.var_declarations {
            self.codegen_vardecl(&decl.ty, decl.id)
        }

        if !self.codegen_block_statement(function.body) {
            self.builder.build_unreachable();
        }
    }

    fn codegen_parameter(
        &mut self,
        ty: &ty::Type,
        id: ir::IdentifierId,
        func: LLVMValueRef,
        index: usize,
    ) {
        let llvm_ty = self.codegen_type(ty);
        let ptr = self.builder.build_alloca(llvm_ty, b"\0");
        let arg_value = utils::get_func_param(func, index);
        self.builder.build_store(arg_value, ptr);
        self.ids.insert(id, ptr);
    }

    fn codegen_block_statement(&mut self, block: ir::BlockStatement) -> bool {
        let mut res = false;
        for statement in block {
            res = self.codegen_statement(statement);
        }
        res
    }

    fn codegen_statement(&mut self, statement: ir::Statement) -> bool {
        // return true if the statement end on a terminator
        match statement {
            ir::Statement::Block(block) => self.codegen_block_statement(block),
            ir::Statement::If {
                condition,
                body,
                else_clause,
            } => self.codegen_if(condition, body, else_clause),
            ir::Statement::While { condition, body } => self.codegen_while(condition, body),
            ir::Statement::Return(expr) => self.codegen_return_statement(expr),
            ir::Statement::Expression(expr) => {
                self.codegen_expression(expr);
                false
            }
            ir::Statement::Break => self.codegen_break_statement(),
            ir::Statement::Continue => self.codegen_continue_statement(),
        }
    }

    fn codegen_vardecl(&mut self, ty: &ty::Type, id: ir::IdentifierId) {
        let llvm_ty = self.codegen_type(ty);
        let ptr = self.builder.build_alloca(llvm_ty, b"\0");
        self.ids.insert(id, ptr);
    }

    fn codegen_if(
        &mut self,
        cond: ir::Expression,
        body: ir::BlockStatement,
        else_clause: ir::BlockStatement,
    ) -> bool {
        let cond = self.codegen_expression(cond);
        let then_bb = self.context.append_bb_to_func(self.current_func, b"then\0");
        let else_bb = self.context.append_bb_to_func(self.current_func, b"else\0");
        let end_bb = self.context.append_bb_to_func(self.current_func, b"end\0");

        self.builder.build_cond_br(cond, then_bb, else_bb);

        let mut then_res = true;
        let mut else_res = true;

        self.builder.position_at_end(then_bb);
        if !self.codegen_block_statement(body) {
            self.builder.build_br(end_bb);
            then_res = false;
        }

        self.builder.position_at_end(else_bb);
        if !self.codegen_block_statement(else_clause) {
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

    fn codegen_while(&mut self, cond: ir::Expression, body: ir::BlockStatement) -> bool {
        let loop_bb = self.context.append_bb_to_func(self.current_func, b"loop\0");
        let then_bb = self.context.append_bb_to_func(self.current_func, b"then\0");
        let end_bb = self.context.append_bb_to_func(self.current_func, b"end\0");

        self.builder.build_br(loop_bb);
        self.builder.position_at_end(loop_bb);
        let cond = self.codegen_expression(cond);
        self.builder.build_cond_br(cond, then_bb, end_bb);

        self.current_break = end_bb;
        self.current_continue = loop_bb;

        self.builder.position_at_end(then_bb);
        if self.codegen_block_statement(body) {
            self.codegen_next_bb();
        }
        self.builder.build_br(loop_bb);
        self.builder.position_at_end(end_bb);
        false
    }

    fn codegen_next_bb(&mut self) {
        let bb = self.context.append_bb_to_func(self.current_func, b"next\0");
        self.builder.position_at_end(bb);
    }

    fn codegen_return_statement(&mut self, expr: Option<ir::Expression>) -> bool {
        if let Some(expr) = expr {
            let expr = self.codegen_expression(expr);
            self.builder.build_ret(expr);
        } else {
            self.builder.build_ret_void();
        }
        true
    }

    fn codegen_break_statement(&mut self) -> bool {
        self.builder.build_br(self.current_break);
        true
    }

    fn codegen_continue_statement(&mut self) -> bool {
        self.builder.build_br(self.current_continue);
        true
    }

    fn codegen_expression(&mut self, expr: ir::Expression) -> LLVMValueRef {
        match expr {
            ir::Expression::Block(block) => self.codegen_expr_block(*block),
            ir::Expression::LValueToRValue(sub) => self.codegen_l2r_expr(*sub),
            ir::Expression::Literal(lit) => self.codegen_literal(lit),
            ir::Expression::Identifier(id) => self.codegen_identifier(id),
            ir::Expression::Assign { lhs, rhs } => self.codegen_assign(*lhs, *rhs),
            ir::Expression::BinaryOperator { binop, lhs, rhs } => {
                self.codegen_binop(binop, *lhs, *rhs)
            }
            ir::Expression::UnaryOperator { unop, sub } => self.codegen_unop(unop, *sub),
            ir::Expression::LValueUnaryOperator { lvalue_unop, sub } => {
                self.codegen_lvalue_unop(lvalue_unop, *sub)
            }
            ir::Expression::Cast { kind, sub } => self.codegen_cast(kind, *sub),
            ir::Expression::BitCast { dest_ty, sub } => self.codegen_bitcast(&dest_ty, *sub),
            ir::Expression::FunctionCall { function, args } => {
                self.codegen_funccall(&function, args)
            }
            ir::Expression::Subscript { ptr, index } => self.codegen_subscript(*ptr, *index),
            _ => unimplemented!(),
        }
    }

    fn codegen_expr_block(&mut self, block: ir::BlockExpression) -> LLVMValueRef {
        for stmt in block.stmts {
            self.codegen_statement(stmt);
        }
        self.codegen_expression(block.final_expr)
    }

    fn codegen_l2r_expr(&mut self, expr: ir::Expression) -> LLVMValueRef {
        let expr = self.codegen_expression(expr);
        self.builder.build_load(expr, b"\0")
    }

    fn codegen_literal(&mut self, literal: common::Literal) -> LLVMValueRef {
        match literal {
            common::Literal::IntLiteral(i) => {
                let ty = self.codegen_type(&ty::Type::Int);
                utils::const_int(ty, i, true)
            }
            common::Literal::DoubleLiteral(d) => {
                let ty = self.codegen_type(&ty::Type::Double);
                utils::const_real(ty, d)
            }
            common::Literal::BooleanLiteral(b) => {
                let ty = self.codegen_type(&ty::Type::Boolean);
                utils::const_int(ty, b as _, false)
            }
            common::Literal::StringLiteral(id) => self.codegen_string_literal(id),
        }
    }

    fn codegen_string_literal(&mut self, id: InternerId) -> LLVMValueRef {
        let s = self.strings.get_ref(id);

        let gs = self.builder.build_global_string_ptr(s.to_string(), b"\0");
        let s_ty = self.codegen_type(&ty::Type::String);
        self.builder.build_bitcast(gs, s_ty, b"\0")
    }

    fn codegen_identifier(&mut self, id: ir::IdentifierId) -> LLVMValueRef {
        self.ids[&id]
    }

    fn codegen_assign(&mut self, lhs: ir::Expression, rhs: ir::Expression) -> LLVMValueRef {
        let lhs = self.codegen_expression(lhs);
        let rhs = self.codegen_expression(rhs);

        self.builder.build_store(rhs, lhs);

        rhs
    }

    fn codegen_binop(
        &mut self,
        binop: ir::BinaryOperatorKind,
        lhs: ir::Expression,
        rhs: ir::Expression,
    ) -> LLVMValueRef {
        let lhs = self.codegen_expression(lhs);
        let rhs = self.codegen_expression(rhs);

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

        fn build_ptr_plus_offset(
            b: &IRBuilder,
            l: LLVMValueRef,
            r: LLVMValueRef,
            n: &[u8],
        ) -> LLVMValueRef {
            b.build_gep(l, vec![r], n)
        }

        fn build_ptr_minus_offset(
            b: &IRBuilder,
            l: LLVMValueRef,
            r: LLVMValueRef,
            n: &[u8],
        ) -> LLVMValueRef {
            let ty = utils::type_of(r);
            let const0 = utils::const_int(ty, 0, false);
            let neg = b.build_sub(const0, r, b"\0");
            b.build_gep(l, vec![neg], n)
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
            bok::PtrPlusOffset => build_ptr_plus_offset,
            bok::PtrMinusOffset => build_ptr_minus_offset,
            bok::PtrDiff => unimplemented!(),
        };

        func(&self.builder, lhs, rhs, b"\0")
    }

    fn codegen_unop(&mut self, unop: ir::UnaryOperatorKind, sub: ir::Expression) -> LLVMValueRef {
        let sub = self.codegen_expression(sub);

        match unop {
            ir::UnaryOperatorKind::IntMinus => {
                let const0 = utils::const_int(self.codegen_type(&ty::Type::Int), 0, false);
                self.builder.build_sub(const0, sub, b"\0")
            }
            ir::UnaryOperatorKind::DoubleMinus => {
                let const0 = utils::const_real(self.codegen_type(&ty::Type::Double), 0.0);
                self.builder.build_fsub(const0, sub, b"\0")
            }
            ir::UnaryOperatorKind::BooleanNot => self.builder.build_not(sub, b"\0"),
            ir::UnaryOperatorKind::PointerDeref => sub,
        }
    }

    fn codegen_lvalue_unop(
        &mut self,
        lvalue_unop: ir::LValueUnaryOperatorKind,
        sub: ir::Expression,
    ) -> LLVMValueRef {
        match lvalue_unop {
            ir::LValueUnaryOperatorKind::IntIncrement => self.codegen_incdecrement(sub, true),
            ir::LValueUnaryOperatorKind::IntDecrement => self.codegen_incdecrement(sub, false),
            ir::LValueUnaryOperatorKind::LValueToPtr => self.codegen_addressof(sub),
        }
    }

    fn codegen_incdecrement(&mut self, sub: ir::Expression, inc: bool) -> LLVMValueRef {
        let ptr = self.codegen_expression(sub);

        let c1 = utils::const_int(self.codegen_type(&ty::Type::Int), 1, true);

        let value = self.builder.build_load(ptr, b"\0");
        let value = if inc {
            self.builder.build_add(value, c1, b"\0")
        } else {
            self.builder.build_sub(value, c1, b"\0")
        };

        self.builder.build_store(value, ptr);

        ptr
    }

    fn codegen_addressof(&mut self, sub: ir::Expression) -> LLVMValueRef {
        self.codegen_expression(sub)
    }

    fn codegen_cast(&mut self, kind: ir::CastKind, sub: ir::Expression) -> LLVMValueRef {
        let sub = self.codegen_expression(sub);

        match kind {
            ir::CastKind::IntToDouble => {
                self.builder
                    .build_si_to_fp(sub, self.codegen_type(&ty::Type::Double), b"\0")
            }
            ir::CastKind::DoubleToInt => {
                self.builder
                    .build_fp_to_si(sub, self.codegen_type(&ty::Type::Int), b"\0")
            }
            ir::CastKind::BooleanToInt => {
                self.builder
                    .build_zext(sub, self.codegen_type(&ty::Type::Int), b"\0")
            }
            ir::CastKind::IntToBoolean => {
                self.builder
                    .build_trunc(sub, self.codegen_type(&ty::Type::Boolean), b"\0")
            }
        }
    }

    fn codegen_bitcast(&mut self, dest_ty: &ty::Type, sub: ir::Expression) -> LLVMValueRef {
        let sub = self.codegen_expression(sub);
        self.builder
            .build_bitcast(sub, self.codegen_type(dest_ty), b"\0")
    }

    fn codegen_subscript(&mut self, ptr: ir::Expression, index: ir::Expression) -> LLVMValueRef {
        let ptr = self.codegen_expression(ptr);
        let index = self.codegen_expression(index);

        self.builder.build_gep(ptr, vec![index], b"\0")
    }

    fn codegen_funccall(&mut self, func: &str, args: Vec<ir::Expression>) -> LLVMValueRef {
        let func = self.module
            .get_named_function(&CString::new(func.to_string()).unwrap());
        let args: Vec<_> = args.into_iter()
            .map(|e| self.codegen_expression(e))
            .collect();

        self.builder.build_call(func, args, b"\0")
    }

    fn into_exec_module(self) -> ExecutionModule {
        ExecutionModule::new(self.context, self.module)
    }
}
