use std;
use std::ptr;
use std::ffi::CString;

use llvm;
use llvm::execution_engine::LLVMExecutionEngineRef;
use llvm::core::*;
use libc;

use backend::helper::{Context, Module};

pub struct ExecutionModule {
    module: Module,
    _context: Context,
}

impl ExecutionModule {
    pub fn new(context: Context, module: Module) -> Self {
        unsafe {
            llvm::target::LLVM_InitializeNativeTarget();
            llvm::target::LLVM_InitializeNativeAsmPrinter();
            // llvm::target::LLVM_InitializeNativeAsmParser();
        }

        ExecutionModule {
            module,
            _context: context,
        }
    }

    pub fn verify_module(&self) {
        unsafe {
            use llvm::analysis::{LLVMVerifierFailureAction, LLVMVerifyModule};
            LLVMVerifyModule(
                self.module.module,
                LLVMVerifierFailureAction::LLVMPrintMessageAction,
                ptr::null_mut(),
            );
        }
    }

    pub fn print_module(&self) {
        unsafe {
            LLVMDumpModule(self.module.module);
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

            LLVMRunPassManager(pass_manager, self.module.module);
            LLVMRunPassManager(pass_manager, self.module.module);

            LLVMDisposePassManager(pass_manager);
        }
    }

    pub fn run_main(&self, exec_engine: LLVMExecutionEngineRef) {
        let main_func = self.module
            .get_named_function(&CString::new("main").unwrap());

        unsafe {
            llvm::execution_engine::LLVMRunFunction(exec_engine, main_func, 0, ptr::null_mut());
        }
    }

    pub fn interpret_main(&self) -> Result<(), CString> {
        /*
        let mut exec_engine: LLVMExecutionEngineRef = std::ptr::null_mut();
        unsafe {
            let mut error: *mut libc::c_char = std::ptr::null_mut();
            llvm::execution_engine::LLVMLinkInInterpreter();
            if llvm::execution_engine::LLVMCreateInterpreterForModule(
                &mut exec_engine,
                self.module.module,
                &mut error,
            ) != 0
            {
                return Err(CString::from_raw(error));
            }
        }

        self.run_main(exec_engine);

        unsafe {
            llvm::execution_engine::LLVMDisposeExecutionEngine(exec_engine);
        }
        Ok(())
        */
        unimplemented!()
    }

    pub fn jit_main(&self) -> Result<(), CString> {
        use llvm::execution_engine::LLVMMCJITCompilerOptions;

        let mut exec_engine: LLVMExecutionEngineRef = std::ptr::null_mut();
        unsafe {
            let mut error: *mut libc::c_char = std::ptr::null_mut();
            let mut options: LLVMMCJITCompilerOptions = std::mem::zeroed();
            let options_size = std::mem::size_of::<LLVMMCJITCompilerOptions>();
            llvm::execution_engine::LLVMInitializeMCJITCompilerOptions(&mut options, options_size);

            options.OptLevel = 3;

            llvm::execution_engine::LLVMLinkInMCJIT();
            if llvm::execution_engine::LLVMCreateMCJITCompilerForModule(
                &mut exec_engine,
                self.module.module,
                &mut options,
                options_size,
                &mut error,
            ) != 0
            {
                return Err(CString::from_raw(error));
            }
        }

        self.run_main(exec_engine);

        unsafe {
            llvm::execution_engine::LLVMDisposeExecutionEngine(exec_engine);
        }
        Ok(())
    }
}
