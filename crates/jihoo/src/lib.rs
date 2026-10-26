// The jihoo compiler.

#![allow(clippy::too_many_arguments, clippy::type_complexity)]

pub mod ast;
pub mod astdump;
pub mod check;
pub mod diag;
pub mod elab;
pub mod lex;
pub mod llvm;
pub mod backend;
pub mod load;
pub mod mir;
pub mod parse;
pub mod sema;
pub mod target;
pub mod types;

use diag::Sources;
use std::path::{Path, PathBuf};

pub struct Options {
    pub search: Vec<PathBuf>,
    pub target: target::Target,
    /// Integer overflow traps.
    pub checked: bool,
    pub no_prelude: bool,
    /// Emit a C-linkable library object, without an entry point.
    pub library: bool,
}

/// Source to MIR, checked and with drops elaborated.
pub fn compile(path: &Path, opts: &Options, sources: &mut Sources) -> Result<mir::Program, diag::Diag> {
    let search = load::default_search(&opts.search);
    let ast = load::load(path, search, opts.target.name(), sources, opts.no_prelude)?;
    let mut prog = sema::compile(&ast, opts.target, opts.checked, opts.library)?;
    if std::env::var("JIHOO_NO_ELAB").is_ok() {
        return Ok(prog);
    }
    for i in 0..prog.fns.len() {
        let mut f = std::mem::replace(&mut prog.fns[i], placeholder());
        let r = elab::run(&mut prog.types, &mut f).and_then(|_| check::run(&prog.types, &f));
        prog.fns[i] = f;
        r?;
    }
    Ok(prog)
}

fn placeholder() -> mir::Function {
    mir::Function {
        symbol: String::new(),
        name: String::new(),
        sig: types::Sig { params: vec![], ret: types::UNIT },
        pass: vec![],
        body: None,
        linkage: mir::Linkage::Internal,
        variadic: false,
        returns_ref: false,
        span: diag::Span::default(),
    }
}

pub fn emit_llvm(prog: &mut mir::Program) -> String {
    llvm::Gen::new(prog).emit()
}
