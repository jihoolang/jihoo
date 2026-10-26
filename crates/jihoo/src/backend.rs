//! LLVM 21 C API, loaded at runtime so the bootstrap has no LLVM build dependency.
//! Keep this backend in step with compiler/backend.jh.

use crate::target::Target;
use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::path::Path;

type Ptr = *mut c_void;

#[link(name = "dl")]
unsafe extern "C" {
    fn dlopen(path: *const c_char, flags: c_int) -> Ptr;
    fn dlsym(handle: Ptr, name: *const c_char) -> Ptr;
    fn dlclose(handle: Ptr) -> c_int;
    fn dlerror() -> *const c_char;
}

struct Library(Ptr);

impl Library {
    fn open() -> Result<Self, String> {
        let names = match std::env::var("JIHOO_LLVM") {
            Ok(p) => vec![p],
            Err(_) => vec![
                "libLLVM-21.so".into(),
                "libLLVM.so.21.1".into(),
                "libLLVM.so".into(),
            ],
        };
        let mut last = String::new();
        for name in names {
            let c = CString::new(name).map_err(|_| "JIHOO_LLVM contains a zero byte")?;
            let h = unsafe { dlopen(c.as_ptr(), 2) };
            if !h.is_null() {
                return Ok(Self(h));
            }
            last = unsafe { CStr::from_ptr(dlerror()) }
                .to_string_lossy()
                .into_owned();
        }
        Err(format!(
            "cannot load LLVM 21: {} (set JIHOO_LLVM to its shared library)",
            last
        ))
    }

    fn symbol(&self, name: &str) -> Result<Ptr, String> {
        let c = CString::new(name).unwrap();
        let p = unsafe { dlsym(self.0, c.as_ptr()) };
        if p.is_null() {
            Err(format!("LLVM 21 is missing {}", name))
        } else {
            Ok(p)
        }
    }
}

impl Drop for Library {
    fn drop(&mut self) {
        unsafe { dlclose(self.0) };
    }
}

// Each declaration is the exact prototype in the LLVM 21 llvm-c headers.
macro_rules! api {
    ($lib:ident, $name:ident, ($($arg:ty),*) -> $ret:ty) => {
        let $name: unsafe extern "C" fn($($arg),*) -> $ret =
            unsafe { std::mem::transmute($lib.symbol(stringify!($name))?) };
    };
}

/// Optimize in memory and emit an object; no clang, opt or llc process.
#[allow(non_snake_case)]
pub fn object(
    ir: &str,
    path: &Path,
    opt: &str,
    target: Target,
    freestanding: bool,
) -> Result<(), String> {
    let lib = Library::open()?;
    api!(lib, LLVMGetVersion, (*mut u32, *mut u32, *mut u32) -> ());
    let mut major = 0;
    unsafe { LLVMGetVersion(&mut major, std::ptr::null_mut(), std::ptr::null_mut()) };
    if major != 21 {
        return Err(format!("expected LLVM 21, found LLVM {}", major));
    }
    let arch = match target {
        Target::X86_64 => "X86",
        Target::Aarch64 => "AArch64",
    };
    for suffix in [
        "TargetInfo",
        "Target",
        "TargetMC",
        "AsmPrinter",
        "AsmParser",
    ] {
        let init: unsafe extern "C" fn() = unsafe {
            std::mem::transmute(lib.symbol(&format!("LLVMInitialize{}{}", arch, suffix))?)
        };
        unsafe { init() };
    }
    api!(lib, LLVMContextCreate, () -> Ptr);
    api!(lib, LLVMContextDispose, (Ptr) -> ());
    api!(lib, LLVMCreateMemoryBufferWithMemoryRangeCopy, (*const u8, usize, *const c_char) -> Ptr);
    api!(lib, LLVMParseIRInContext, (Ptr, Ptr, *mut Ptr, *mut *mut c_char) -> c_int);
    api!(lib, LLVMDisposeModule, (Ptr) -> ());
    api!(lib, LLVMDisposeMessage, (*mut c_char) -> ());
    api!(lib, LLVMVerifyModule, (Ptr, c_int, *mut *mut c_char) -> c_int);
    api!(lib, LLVMGetTargetFromTriple, (*const c_char, *mut Ptr, *mut *mut c_char) -> c_int);
    api!(lib, LLVMCreateTargetMachine, (Ptr, *const c_char, *const c_char, *const c_char, c_int, c_int, c_int) -> Ptr);
    api!(lib, LLVMDisposeTargetMachine, (Ptr) -> ());
    api!(lib, LLVMCreateTargetDataLayout, (Ptr) -> Ptr);
    api!(lib, LLVMSetModuleDataLayout, (Ptr, Ptr) -> ());
    api!(lib, LLVMDisposeTargetData, (Ptr) -> ());
    api!(lib, LLVMCreatePassBuilderOptions, () -> Ptr);
    api!(lib, LLVMDisposePassBuilderOptions, (Ptr) -> ());
    api!(lib, LLVMPassBuilderOptionsSetLoopVectorization, (Ptr, c_int) -> ());
    api!(lib, LLVMPassBuilderOptionsSetSLPVectorization, (Ptr, c_int) -> ());
    api!(lib, LLVMRunPasses, (Ptr, *const c_char, Ptr, Ptr) -> Ptr);
    api!(lib, LLVMGetErrorMessage, (Ptr) -> *mut c_char);
    api!(lib, LLVMDisposeErrorMessage, (*mut c_char) -> ());
    api!(lib, LLVMTargetMachineEmitToFile, (Ptr, Ptr, *const c_char, c_int, *mut *mut c_char) -> c_int);
    api!(lib, LLVMGetFirstFunction, (Ptr) -> Ptr);
    api!(lib, LLVMGetNextFunction, (Ptr) -> Ptr);
    api!(lib, LLVMSetSection, (Ptr, *const c_char) -> ());

    let triple = CString::new(target.triple()).unwrap();
    let cpu = if target == Target::X86_64 {
        c"x86-64"
    } else {
        c"generic"
    };
    let level = opt.as_bytes()[2] - b'0';
    let pipeline = CString::new(format!("default<O{}>", level)).unwrap();
    let path = CString::new(path.as_os_str().as_encoded_bytes())
        .map_err(|_| "object path contains a zero byte")?;
    let mut message = std::ptr::null_mut();
    let mut module = std::ptr::null_mut();
    let mut machine = std::ptr::null_mut();
    let ctx = unsafe { LLVMContextCreate() };
    let take_message = |p: *mut c_char| {
        if p.is_null() {
            return "unknown LLVM error".into();
        }
        let s = unsafe { CStr::from_ptr(p) }.to_string_lossy().into_owned();
        unsafe { LLVMDisposeMessage(p) };
        s
    };
    // All resources created below are disposed even when LLVM reports an error.
    let result = (|| unsafe {
        let buffer =
            LLVMCreateMemoryBufferWithMemoryRangeCopy(ir.as_ptr(), ir.len(), c"jihoo".as_ptr());
        // ParseIR takes ownership of the buffer, including on failure.
        if LLVMParseIRInContext(ctx, buffer, &mut module, &mut message) != 0 {
            return Err(format!("LLVM IR: {}", take_message(message)));
        }
        if LLVMVerifyModule(module, 2, &mut message) != 0 {
            return Err(format!("LLVM verification: {}", take_message(message)));
        }
        if !message.is_null() {
            LLVMDisposeMessage(message);
            message = std::ptr::null_mut();
        }
        let mut tgt = std::ptr::null_mut();
        if LLVMGetTargetFromTriple(triple.as_ptr(), &mut tgt, &mut message) != 0 {
            return Err(format!("LLVM target: {}", take_message(message)));
        }
        // PIC matches clang's native Linux defaults, and works for static
        // freestanding binaries too. Keep the portable CPU used by clang.
        machine = LLVMCreateTargetMachine(
            tgt,
            triple.as_ptr(),
            cpu.as_ptr(),
            c"".as_ptr(),
            level as c_int,
            2,
            0,
        );
        if machine.is_null() {
            return Err("LLVM cannot create target machine".into());
        }
        let data = LLVMCreateTargetDataLayout(machine);
        LLVMSetModuleDataLayout(module, data);
        LLVMDisposeTargetData(data);
        let options = LLVMCreatePassBuilderOptions();
        // PassBuilder C API defaults differ from clang's vectorizer setup.
        LLVMPassBuilderOptionsSetLoopVectorization(options, (level >= 2) as c_int);
        LLVMPassBuilderOptionsSetSLPVectorization(options, (level >= 2) as c_int);
        let error = LLVMRunPasses(module, pipeline.as_ptr(), machine, options);
        LLVMDisposePassBuilderOptions(options);
        if !error.is_null() {
            let p = LLVMGetErrorMessage(error);
            let s = CStr::from_ptr(p).to_string_lossy().into_owned();
            LLVMDisposeErrorMessage(p);
            return Err(format!("LLVM optimization: {}", s));
        }
        if freestanding {
            // Equivalent to clang -ffunction-sections, for --gc-sections.
            let mut f = LLVMGetFirstFunction(module);
            let mut i = 0;
            while !f.is_null() {
                let section = CString::new(format!(".text.jihoo.{}", i)).unwrap();
                LLVMSetSection(f, section.as_ptr());
                f = LLVMGetNextFunction(f);
                i += 1;
            }
        }
        if LLVMTargetMachineEmitToFile(machine, module, path.as_ptr(), 1, &mut message) != 0 {
            return Err(format!("LLVM object: {}", take_message(message)));
        }
        Ok(())
    })();
    unsafe {
        if !machine.is_null() {
            LLVMDisposeTargetMachine(machine);
        }
        if !module.is_null() {
            LLVMDisposeModule(module);
        }
        LLVMContextDispose(ctx);
    }
    result
}
