// Code generation: MIR to LLVM IR text, which clang compiles.
//
// Simple on purpose: every local is an alloca, every field a byte offset,
// every aggregate copy a memcpy; mem2reg and SROA turn that into registers.
// Aggregates are passed by pointer and returned through `sret`. Borrows
// are pointers marked `noalias` (an `inout` parameter cannot alias anything:
// the checker made sure).

use crate::lex::Op;
use crate::mir::*;
use crate::target::Target;
use crate::types::{self, TyId, TyKind, Types};
use std::collections::HashMap;
use std::fmt::Write;

pub struct Gen<'p> {
    p: &'p mut Program,
    out: String,
    globals: String,
    strs: HashMap<Vec<u8>, usize>,
    drop_glue: HashMap<TyId, String>,
    glue_todo: Vec<TyId>,
    nstr: usize,
    /// User `Drop` impls, by type.
    pub drop_impls: HashMap<TyId, FnId>,
    declared: HashMap<String, String>,
}

/// An operand's value: a scalar in a register, or an aggregate in memory.
#[derive(Clone, Debug)]
enum V {
    Imm(String),
    Mem(String),
    Zst,
    /// All zero bytes (aggregates).
    Zero,
}

struct FnCx {
    body: String,
    tmp: usize,
    locals: Vec<String>,
    sret: Option<String>,
    trap_block: Option<String>,
}

impl FnCx {
    fn t(&mut self) -> String {
        self.tmp += 1;
        format!("%t{}", self.tmp)
    }
    fn line(&mut self, s: &str) {
        self.body.push_str("  ");
        self.body.push_str(s);
        self.body.push('\n');
    }
}

pub fn esc(bytes: &[u8]) -> String {
    let mut s = String::new();
    for &b in bytes {
        if b.is_ascii_graphic() && b != b'"' && b != b'\\' || b == b' ' {
            s.push(b as char);
        } else {
            let _ = write!(s, "\\{:02X}", b);
        }
    }
    s
}

fn sym(s: &str) -> String {
    format!("@\"{}\"", s.replace('"', "_"))
}

impl<'p> Gen<'p> {
    pub fn new(p: &'p mut Program) -> Gen<'p> {
        let drop_impls = p.drop_impls.clone();
        Gen {
            p,
            out: String::new(),
            globals: String::new(),
            strs: HashMap::new(),
            drop_glue: HashMap::new(),
            glue_todo: Vec::new(),
            nstr: 0,
            drop_impls,
            declared: HashMap::new(),
        }
    }

    fn ty(&mut self) -> &mut Types {
        &mut self.p.types
    }

    /// The LLVM type of a scalar in a register.
    fn scalar(&self, t: TyId) -> String {
        match self.p.types.kind(t) {
            TyKind::Bool => "i1".into(),
            TyKind::Int(i) => format!("i{}", i.bits),
            TyKind::Float(32) => "float".into(),
            TyKind::Float(_) => "double".into(),
            TyKind::Ptr(_) | TyKind::Ref(_) | TyKind::RefMut(_) | TyKind::FnPtr(_) => "ptr".into(),
            k => panic!("not a scalar: {:?}", k),
        }
    }

    /// The LLVM type of a scalar in memory (bools are bytes).
    fn mem_scalar(&self, t: TyId) -> String {
        if t == types::BOOL {
            "i8".into()
        } else {
            self.scalar(t)
        }
    }

    fn is_scalar(&self, t: TyId) -> bool {
        self.p.types.is_scalar(t)
    }

    fn size(&mut self, t: TyId) -> u64 {
        self.ty().layout(t).size
    }
    fn align(&mut self, t: TyId) -> u64 {
        self.ty().layout(t).align
    }

    pub fn emit(mut self) -> String {
        let triple = self.p.target.triple();
        let mut head = String::new();
        let _ = writeln!(head, "; jihoo");
        let _ = writeln!(head, "target triple = \"{}\"", triple);
        let _ = writeln!(head);
        self.globals.push_str("@jihoo.argc = internal global i64 0\n@jihoo.argv = internal global ptr null\n");
        for i in 0..self.p.statics.len() {
            let (name, t, c) = self.p.statics[i].clone();
            if name.is_empty() {
                continue;
            }
            let size = self.size(t).max(1);
            let align = self.align(t);
            let init = match (&c, self.is_scalar(t)) {
                (Const::Zeroed(_), _) | (Const::Zst(_), _) => format!("[{} x i8] zeroinitializer", size),
                (Const::Null(_), _) => "ptr null".to_string(),
                (Const::Int(v, _), true) => format!("{} {}", self.mem_scalar(t), v),
                (Const::Bool(b), true) => format!("i8 {}", *b as u8),
                (Const::Float(..), true) => match self.constant(&c) {
                    V::Imm(x) => format!("{} {}", self.scalar(t), x),
                    _ => unreachable!(),
                },
                _ => format!("[{} x i8] zeroinitializer", size),
            };
            let _ = writeln!(self.globals, "{} = internal global {}, align {}", sym(&name), init, align);
        }
        for i in 0..self.p.fns.len() {
            self.function(i as FnId);
        }
        while let Some(t) = self.glue_todo.pop() {
            self.glue(t);
        }
        self.entry();
        self.runtime();
        let mut decls = String::new();
        for d in self.declared.values() {
            decls.push_str(d);
            decls.push('\n');
        }
        head + &self.globals + "\n" + &decls + "\n" + &self.out
    }

    fn declare(&mut self, name: &str, decl: &str) {
        self.declared.entry(name.to_string()).or_insert_with(|| decl.to_string());
    }

    // ---- signatures ----

    /// The LLVM parameter list and return type of a function.
    fn signature(&mut self, f: FnId) -> (String, Vec<String>, bool) {
        let fun = self.p.fns[f as usize].clone();
        let c_abi = fun.linkage != Linkage::Internal;
        let ret = fun.sig.ret;
        let mut params = Vec::new();
        let mut sret = false;
        let rty = if ret == types::NEVER || self.ty().is_zst(ret) {
            "void".to_string()
        } else if self.is_scalar(ret) {
            if c_abi && ret == types::BOOL {
                "zeroext i1".into()
            } else {
                self.scalar(ret)
            }
        } else {
            sret = true;
            let s = self.size(ret);
            let a = self.align(ret);
            params.push(format!("ptr noalias sret([{} x i8]) align {} dereferenceable({})", s, a, s));
            "void".into()
        };
        for (i, &t) in fun.sig.params.iter().enumerate() {
            let pass = fun.pass.get(i).copied().unwrap_or(ParamPass::Value);
            params.push(self.param_ty(t, pass, c_abi));
        }
        (rty, params, sret)
    }

    fn param_ty(&mut self, t: TyId, pass: ParamPass, c_abi: bool) -> String {
        if self.is_scalar(t) {
            let mut s = self.scalar(t);
            if c_abi && t == types::BOOL {
                s = "zeroext i1".into();
            }
            if pass == ParamPass::Borrow {
                let inner = self.p.types.pointee(t).unwrap();
                let size = self.size(inner);
                let align = self.align(inner);
                let ro = matches!(self.p.types.kind(t), TyKind::Ref(_));
                s = format!("ptr noalias{} align {}{}", if ro { " readonly" } else { "" }, align, if size > 0 { format!(" dereferenceable({})", size) } else { String::new() });
            }
            s
        } else {
            // Aggregates (and values without bytes) go by pointer.
            "ptr".into()
        }
    }

    // ---- functions ----

    fn function(&mut self, f: FnId) {
        let fun = self.p.fns[f as usize].clone();
        let (rty, params, sret) = self.signature(f);
        let Some(body) = &fun.body else {
            // An extern declaration.
            let mut ps: Vec<String> = params.clone();
            if fun.variadic {
                ps.push("...".into());
            }
            self.declare(&fun.symbol, &format!("declare {} {}({})", rty, sym(&fun.symbol), ps.join(", ")));
            return;
        };
        let linkage = match fun.linkage {
            Linkage::Internal => "internal ",
            _ => "",
        };
        // A function that never returns is a way out of the program (a
        // panic): keep it out of the hot path.
        let attrs = if fun.sig.ret == types::NEVER { " cold noreturn" } else { "" };
        let mut cx = FnCx { body: String::new(), tmp: 0, locals: Vec::new(), sret: None, trap_block: None };
        let mut names = Vec::new();
        if sret {
            names.push("ptr %sret".to_string());
            cx.sret = Some("%sret".into());
        }
        for (pi, p) in params.iter().skip(sret as usize).enumerate() {
            names.push(format!("{} %p{}", p, pi));
        }
        let _ = writeln!(self.out, "define {}{} {}({}){} {{", linkage, rty, sym(&fun.symbol), names.join(", "), attrs);
        self.out.push_str("entry:\n");
        // Allocas.
        for (i, l) in body.locals.iter().enumerate() {
            let t = l.ty;
            if i == 0 && sret {
                cx.locals.push("%sret".into());
                continue;
            }
            let is_arg = l.kind == LocalKind::Arg;
            let arg_idx = i.wrapping_sub(1);
            if is_arg && !self.is_scalar(t) && fun.pass.get(arg_idx).copied() == Some(ParamPass::Owned) {
                cx.locals.push(format!("%p{}", arg_idx));
                continue;
            }
            let size = self.size(t).max(1);
            let align = self.align(t);
            let name = format!("%l{}", i);
            cx.line(&format!("{} = alloca [{} x i8], align {}", name, size, align));
            cx.locals.push(name);
        }
        // Store incoming arguments.
        for (i, l) in body.locals.iter().enumerate() {
            if l.kind != LocalKind::Arg {
                continue;
            }
            let arg_idx = i - 1;
            let t = l.ty;
            if self.is_scalar(t) {
                let v = format!("%p{}", arg_idx);
                let dst = cx.locals[i].clone();
                self.store_scalar(&mut cx, t, &v, &dst);
            } else if fun.pass.get(arg_idx).copied() != Some(ParamPass::Owned) && !self.ty().is_zst(t) {
                let s = self.size(t);
                let a = self.align(t);
                let dst = cx.locals[i].clone();
                cx.line(&format!("call void @llvm.memcpy.p0.p0.i64(ptr align {} {}, ptr align {} %p{}, i64 {}, i1 false)", a, dst, a, arg_idx, s));
            }
        }
        cx.line("br label %bb0");
        for (bi, b) in body.blocks.iter().enumerate() {
            cx.body.push_str(&format!("bb{}:\n", bi));
            for s in &b.stmts {
                self.stmt(&mut cx, body, s);
            }
            self.term(&mut cx, f, body, &b.term);
        }
        if let Some(tb) = cx.trap_block.clone() {
            cx.body.push_str(&format!("{}:\n", &tb[1..]));
            cx.line("call void @llvm.trap()");
            cx.line("unreachable");
        }
        self.out.push_str(&cx.body);
        self.out.push_str("}\n\n");
    }

    fn store_scalar(&mut self, cx: &mut FnCx, t: TyId, v: &str, ptr: &str) {
        if t == types::BOOL {
            let z = cx.t();
            cx.line(&format!("{} = zext i1 {} to i8", z, v));
            cx.line(&format!("store i8 {}, ptr {}", z, ptr));
        } else {
            let lt = self.scalar(t);
            cx.line(&format!("store {} {}, ptr {}", lt, v, ptr));
        }
    }

    fn load_scalar(&mut self, cx: &mut FnCx, t: TyId, ptr: &str) -> String {
        if t == types::BOOL {
            let b = cx.t();
            cx.line(&format!("{} = load i8, ptr {}", b, ptr));
            let r = cx.t();
            cx.line(&format!("{} = trunc i8 {} to i1", r, b));
            r
        } else {
            let lt = self.scalar(t);
            let r = cx.t();
            cx.line(&format!("{} = load {}, ptr {}", r, lt, ptr));
            r
        }
    }

    fn gep(&mut self, cx: &mut FnCx, ptr: &str, off: u64) -> String {
        if off == 0 {
            return ptr.to_string();
        }
        let r = cx.t();
        cx.line(&format!("{} = getelementptr inbounds i8, ptr {}, i64 {}", r, ptr, off));
        r
    }

    /// The address of a place, and its type.
    fn place(&mut self, cx: &mut FnCx, body: &Body, p: &Place) -> (String, TyId) {
        let mut ptr = cx.locals[p.local as usize].clone();
        let mut t = body.locals[p.local as usize].ty;
        let mut variant: Option<u32> = None;
        for pr in &p.proj {
            match pr {
                Proj::Deref => {
                    let r = cx.t();
                    cx.line(&format!("{} = load ptr, ptr {}", r, ptr));
                    ptr = r;
                    t = self.p.types.pointee(t).unwrap();
                }
                Proj::Variant(v) => variant = Some(*v),
                Proj::Field(i) => {
                    if let Some(v) = variant.take() {
                        let (_, el) = self.ty().enum_layout(t);
                        let off = el.fields[v as usize][*i as usize];
                        let ft = self.p.types.variants(t).unwrap()[v as usize].fields[*i as usize];
                        ptr = self.gep(cx, &ptr, off);
                        t = ft;
                    } else {
                        let offs = self.ty().field_offsets(t);
                        let off = offs[*i as usize];
                        let ft = match self.p.types.kind(t).clone() {
                            TyKind::Slice(e) => {
                                if *i == 0 {
                                    self.ty().ptr(e)
                                } else {
                                    types::I64
                                }
                            }
                            TyKind::Str => {
                                if *i == 0 {
                                    self.ty().ptr(types::U8)
                                } else {
                                    types::I64
                                }
                            }
                            TyKind::Closure(_) => self.ty().ptr(types::U8),
                            _ => self.p.types.field_tys(t)[*i as usize],
                        };
                        ptr = self.gep(cx, &ptr, off);
                        t = ft;
                    }
                }
                Proj::Index(l) => {
                    let TyKind::Array(e, _) = self.p.types.kind(t).clone() else { panic!("index of non-array") };
                    let es = self.size(e);
                    let ip = cx.locals[*l as usize].clone();
                    let it = body.locals[*l as usize].ty;
                    let iv = self.load_scalar(cx, it, &ip);
                    let iv64 = self.widen_i64(cx, &iv, it);
                    let off = cx.t();
                    cx.line(&format!("{} = mul i64 {}, {}", off, iv64, es));
                    let r = cx.t();
                    cx.line(&format!("{} = getelementptr inbounds i8, ptr {}, i64 {}", r, ptr, off));
                    ptr = r;
                    t = e;
                }
            }
        }
        (ptr, t)
    }

    fn widen_i64(&mut self, cx: &mut FnCx, v: &str, t: TyId) -> String {
        let Some(i) = self.p.types.int(t) else { return v.to_string() };
        if i.bits == 64 {
            return v.to_string();
        }
        let r = cx.t();
        cx.line(&format!("{} = {} i{} {} to i64", r, if i.signed { "sext" } else { "zext" }, i.bits, v));
        r
    }

    fn operand_ty(&mut self, body: &Body, o: &Operand) -> TyId {
        match o {
            Operand::Copy(p) | Operand::Move(p) => self.place_ty(body, p),
            Operand::Const(c) => match c {
                Const::Int(_, t) | Const::Float(_, t) | Const::Zst(t) | Const::Null(t) | Const::Zeroed(t) | Const::Bytes(_, t) | Const::Static(_, t) => *t,
                Const::Bool(_) => types::BOOL,
                Const::Str(_) => types::STR,
                Const::Fn(f) => {
                    let sig = self.p.fns[*f as usize].sig.clone();
                    self.ty().intern(TyKind::FnPtr(sig))
                }
            },
        }
    }

    fn place_ty(&mut self, body: &Body, p: &Place) -> TyId {
        let mut t = body.locals[p.local as usize].ty;
        let mut variant: Option<u32> = None;
        for pr in &p.proj {
            t = match pr {
                Proj::Deref => self.p.types.pointee(t).unwrap(),
                Proj::Variant(v) => {
                    variant = Some(*v);
                    continue;
                }
                Proj::Field(i) => {
                    if let Some(v) = variant.take() {
                        self.p.types.variants(t).unwrap()[v as usize].fields[*i as usize]
                    } else {
                        match self.p.types.kind(t).clone() {
                            TyKind::Slice(e) => {
                                if *i == 0 {
                                    self.ty().ptr(e)
                                } else {
                                    types::I64
                                }
                            }
                            TyKind::Str => {
                                if *i == 0 {
                                    self.ty().ptr(types::U8)
                                } else {
                                    types::I64
                                }
                            }
                            TyKind::Closure(_) => self.ty().ptr(types::U8),
                            _ => self.p.types.field_tys(t)[*i as usize],
                        }
                    }
                }
                Proj::Index(_) => match self.p.types.kind(t) {
                    TyKind::Array(e, _) => *e,
                    _ => panic!(),
                },
            };
        }
        t
    }

    fn str_global(&mut self, s: &[u8]) -> (String, usize) {
        if let Some(&n) = self.strs.get(s) {
            return (format!("@.str.{}", n), s.len());
        }
        let n = self.nstr;
        self.nstr += 1;
        // A zero after the bytes, so that a literal is also a C string.
        let _ = writeln!(self.globals, "@.str.{} = private unnamed_addr constant [{} x i8] c\"{}\\00\", align 1", n, s.len() + 1, esc(s));
        let _ = writeln!(self.globals, "@.strv.{} = private unnamed_addr constant {{ ptr, i64 }} {{ ptr @.str.{}, i64 {} }}, align 8", n, n, s.len());
        self.strs.insert(s.to_vec(), n);
        (format!("@.str.{}", n), s.len())
    }

    fn operand(&mut self, cx: &mut FnCx, body: &Body, o: &Operand) -> V {
        match o {
            Operand::Copy(p) | Operand::Move(p) => {
                let (ptr, t) = self.place(cx, body, p);
                if self.ty().is_zst(t) {
                    V::Zst
                } else if self.is_scalar(t) {
                    V::Imm(self.load_scalar(cx, t, &ptr))
                } else {
                    V::Mem(ptr)
                }
            }
            Operand::Const(c) => self.constant(c),
        }
    }

    fn constant(&mut self, c: &Const) -> V {
        match c {
            Const::Int(v, t) => {
                let _ = t;
                V::Imm(v.to_string())
            }
            Const::Float(f, t) => {
                // LLVM wants a double's bits in hex, also for floats.
                let bits = if *t == types::F32 { (*f as f32 as f64).to_bits() } else { f.to_bits() };
                V::Imm(format!("0x{:016X}", bits))
            }
            Const::Bool(b) => V::Imm(if *b { "true".into() } else { "false".into() }),
            Const::Zst(_) => V::Zst,
            Const::Str(s) => {
                let (_, _) = self.str_global(s);
                let n = self.strs[s];
                V::Mem(format!("@.strv.{}", n))
            }
            Const::Fn(f) => V::Imm(sym(&self.p.fns[*f as usize].symbol)),
            Const::Null(_) => V::Imm("null".into()),
            Const::Zeroed(t) => {
                if self.is_scalar(*t) {
                    V::Imm(match self.p.types.kind(*t) {
                        TyKind::Float(_) => "0.0".into(),
                        TyKind::Bool => "false".into(),
                        TyKind::Int(_) => "0".into(),
                        _ => "null".into(),
                    })
                } else {
                    V::Zero
                }
            }
            Const::Static(i, _) => V::Imm(sym(&self.p.statics[*i as usize].0)),
            Const::Bytes(b, _) => {
                let n = self.nstr;
                self.nstr += 1;
                let _ = writeln!(self.globals, "@.bytes.{} = private unnamed_addr constant [{} x i8] c\"{}\", align 16", n, b.len(), esc(b));
                V::Mem(format!("@.bytes.{}", n))
            }
        }
    }

    /// Stores a value into memory of type t.
    fn store(&mut self, cx: &mut FnCx, t: TyId, v: V, dst: &str) {
        match v {
            V::Zst => {}
            V::Imm(x) => self.store_scalar(cx, t, &x, dst),
            V::Mem(src) => {
                if src == dst {
                    return;
                }
                let s = self.size(t);
                let a = self.align(t);
                cx.line(&format!("call void @llvm.memcpy.p0.p0.i64(ptr align {} {}, ptr align {} {}, i64 {}, i1 false)", a, dst, a, src, s));
            }
            V::Zero => {
                let s = self.size(t);
                let a = self.align(t);
                cx.line(&format!("call void @llvm.memset.p0.i64(ptr align {} {}, i8 0, i64 {}, i1 false)", a, dst, s));
            }
        }
    }

    fn imm(&mut self, cx: &mut FnCx, v: V, t: TyId) -> String {
        match v {
            V::Imm(x) => x,
            V::Mem(p) => self.load_scalar(cx, t, &p),
            V::Zero => "0".into(),
            V::Zst => "undef".into(),
        }
    }

    fn panic_msg(&mut self, cx: &mut FnCx, msg: &str) {
        let (g, n) = self.str_global(msg.as_bytes());
        cx.line(&format!("call void @jihoo.panic(ptr {}, i64 {})", g, n));
        cx.line("unreachable");
    }

    fn stmt(&mut self, cx: &mut FnCx, body: &Body, s: &Stmt) {
        match s {
            Stmt::Assign(p, r, _) => self.assign(cx, body, p, r),
            Stmt::Drop(p, _) => {
                let (ptr, t) = self.place(cx, body, p);
                self.call_drop(cx, t, &ptr);
            }
            Stmt::StorageLive(_) | Stmt::StorageDead(_) | Stmt::Forget(_) | Stmt::Nop => {}
        }
    }

    fn call_drop(&mut self, cx: &mut FnCx, t: TyId, ptr: &str) {
        if !self.ty().needs_drop(t) {
            return;
        }
        let g = self.glue_name(t);
        cx.line(&format!("call void {}(ptr {})", g, ptr));
    }

    fn glue_name(&mut self, t: TyId) -> String {
        if let Some(g) = self.drop_glue.get(&t) {
            return g.clone();
        }
        let g = format!("@\"drop.{}\"", self.drop_glue.len());
        self.drop_glue.insert(t, g.clone());
        self.glue_todo.push(t);
        g
    }

    /// A function that drops a value of type t at a pointer: the user's
    /// `drop`, then the parts.
    fn glue(&mut self, t: TyId) {
        let g = self.drop_glue[&t].clone();
        let mut cx = FnCx { body: String::new(), tmp: 0, locals: Vec::new(), sret: None, trap_block: None };
        if let Some(&f) = self.drop_impls.get(&t) {
            cx.line(&format!("call void {}(ptr %p)", sym(&self.p.fns[f as usize].symbol)));
        }
        match self.p.types.kind(t).clone() {
            TyKind::Tuple(ts) => {
                let offs = self.ty().field_offsets(t);
                for (i, ft) in ts.into_iter().enumerate() {
                    let p = self.gep(&mut cx, "%p", offs[i]);
                    self.call_drop(&mut cx, ft, &p);
                }
            }
            TyKind::Array(e, n) => {
                let es = self.size(e);
                for i in 0..n {
                    let p = self.gep(&mut cx, "%p", i * es);
                    self.call_drop(&mut cx, e, &p);
                }
            }
            TyKind::Adt(_) => {
                if let Some(vs) = self.p.types.variants(t).cloned() {
                    let (_, el) = self.ty().enum_layout(t);
                    let tag = cx.t();
                    cx.line(&format!("{} = load i{}, ptr %p", tag, el.tag_bits));
                    let mut cases = String::new();
                    let mut blocks = String::new();
                    for (vi, v) in vs.iter().enumerate() {
                        let mut inner = FnCx { body: String::new(), tmp: cx.tmp + 1000 * (vi + 1), locals: Vec::new(), sret: None, trap_block: None };
                        let mut any = false;
                        for (fi, &ft) in v.fields.iter().enumerate() {
                            if self.ty().needs_drop(ft) {
                                any = true;
                                let p = self.gep(&mut inner, "%p", el.fields[vi][fi]);
                                self.call_drop(&mut inner, ft, &p);
                            }
                        }
                        if any {
                            let _ = write!(cases, " i{} {}, label %v{}", el.tag_bits, vi, vi);
                            blocks.push_str(&format!("v{}:\n", vi));
                            blocks.push_str(&inner.body);
                            blocks.push_str("  br label %done\n");
                        }
                    }
                    cx.line(&format!("switch i{} {}, label %done [{} ]", el.tag_bits, tag, cases));
                    cx.body.push_str(&blocks);
                    cx.body.push_str("done:\n");
                } else {
                    let offs = self.ty().field_offsets(t);
                    for (i, ft) in self.p.types.field_tys(t).into_iter().enumerate() {
                        let p = self.gep(&mut cx, "%p", offs[i]);
                        self.call_drop(&mut cx, ft, &p);
                    }
                }
            }
            _ => {}
        }
        cx.line("ret void");
        let _ = writeln!(self.out, "define internal void {}(ptr %p) {{\nentry:\n{}}}\n", g, cx.body);
    }

    fn assign(&mut self, cx: &mut FnCx, body: &Body, p: &Place, r: &Rvalue) {
        let (dst, t) = self.place(cx, body, p);
        match r {
            Rvalue::Use(o) => {
                let v = self.operand(cx, body, o);
                self.store(cx, t, v, &dst);
            }
            Rvalue::Bin(op, a, b) => {
                let at = self.operand_ty(body, a);
                let av = self.operand(cx, body, a);
                let bv = self.operand(cx, body, b);
                let av = self.imm(cx, av, at);
                let bt = self.operand_ty(body, b);
                let bv = self.imm(cx, bv, bt);
                let r = self.binop(cx, *op, at, &av, &bv);
                self.store_scalar(cx, t, &r, &dst);
            }
            Rvalue::Un(op, a) => {
                let at = self.operand_ty(body, a);
                let av = self.operand(cx, body, a);
                let av = self.imm(cx, av, at);
                let lt = self.scalar(at);
                let r = cx.t();
                match (op, self.p.types.kind(at)) {
                    (UnOp::Neg, TyKind::Float(_)) => cx.line(&format!("{} = fneg {} {}", r, lt, av)),
                    (UnOp::Neg, _) => cx.line(&format!("{} = sub {} 0, {}", r, lt, av)),
                    (UnOp::Not, TyKind::Bool) => cx.line(&format!("{} = xor i1 {}, true", r, av)),
                    (UnOp::Not, _) => cx.line(&format!("{} = xor {} {}, -1", r, lt, av)),
                }
                self.store_scalar(cx, t, &r, &dst);
            }
            Rvalue::Cast(a, to, _) => {
                let at = self.operand_ty(body, a);
                let av = self.operand(cx, body, a);
                let av = self.imm(cx, av, at);
                let r = self.cast(cx, &av, at, *to);
                self.store_scalar(cx, t, &r, &dst);
            }
            Rvalue::Ref(q) | Rvalue::RefMut(q) | Rvalue::Addr(q) => {
                let (qp, _) = self.place(cx, body, q);
                cx.line(&format!("store ptr {}, ptr {}", qp, dst));
            }
            Rvalue::Aggregate(kind, ops) => self.aggregate(cx, body, kind, ops, &dst, t),
            Rvalue::Discriminant(q) => {
                let (qp, qt) = self.place(cx, body, q);
                let (_, el) = self.ty().enum_layout(qt);
                let tag = cx.t();
                cx.line(&format!("{} = load i{}, ptr {}", tag, el.tag_bits, qp));
                let lt = self.scalar(t);
                let bits = self.p.types.int(t).map(|i| i.bits).unwrap_or(64);
                let r = if bits > el.tag_bits {
                    let r = cx.t();
                    cx.line(&format!("{} = zext i{} {} to {}", r, el.tag_bits, tag, lt));
                    r
                } else {
                    tag
                };
                self.store_scalar(cx, t, &r, &dst);
            }
            Rvalue::Offset(a, b) => {
                let at = self.operand_ty(body, a);
                let bt = self.operand_ty(body, b);
                let av = self.operand(cx, body, a);
                let av = self.imm(cx, av, at);
                let bv = self.operand(cx, body, b);
                let bv = self.imm(cx, bv, bt);
                let e = self.p.types.pointee(at).unwrap();
                let es = self.size(e);
                let r = cx.t();
                if es == 0 {
                    cx.line(&format!("{} = getelementptr i8, ptr {}, i64 0", r, av));
                } else {
                    cx.line(&format!("{} = getelementptr inbounds [{} x i8], ptr {}, i64 {}", r, es, av, bv));
                }
                cx.line(&format!("store ptr {}, ptr {}", r, dst));
            }
            Rvalue::Repeat(o, n) => {
                let TyKind::Array(e, _) = self.p.types.kind(t).clone() else { panic!() };
                let es = self.size(e);
                let v = self.operand(cx, body, o);
                if *n == 0 || es == 0 {
                    return;
                }
                if let V::Imm(x) = &v {
                    if (x == "0" || x == "false" || x == "null") && !self.p.types.is_float(e) {
                        let s = self.size(t);
                        cx.line(&format!("call void @llvm.memset.p0.i64(ptr {}, i8 0, i64 {}, i1 false)", dst, s));
                        return;
                    }
                }
                if *n <= 16 {
                    for i in 0..*n {
                        let p = self.gep(cx, &dst, i * es);
                        self.store(cx, e, v.clone(), &p);
                    }
                    return;
                }
                // A loop.
                let id = cx.t().replace('%', "");
                let i = cx.t();
                let inext = cx.t();
                let cur = cx.label_block();
                cx.line(&format!("br label %{}.head", id));
                cx.body.push_str(&format!("{}.head:\n", id));
                cx.line(&format!("{} = phi i64 [ 0, %{} ], [ {}, %{}.head ]", i, cur, inext, id));
                let off = cx.t();
                cx.line(&format!("{} = mul i64 {}, {}", off, i, es));
                let p = cx.t();
                cx.line(&format!("{} = getelementptr inbounds i8, ptr {}, i64 {}", p, dst, off));
                self.store(cx, e, v, &p);
                cx.line(&format!("{} = add i64 {}, 1", inext, i));
                let c = cx.t();
                cx.line(&format!("{} = icmp ult i64 {}, {}", c, inext, n));
                cx.line(&format!("br i1 {}, label %{}.head, label %{}.done", c, id, id));
                cx.body.push_str(&format!("{}.done:\n", id));
                cx.set_block(&format!("{}.done", id));
            }
        }
    }

    fn aggregate(&mut self, cx: &mut FnCx, body: &Body, kind: &Agg, ops: &[Operand], dst: &str, t: TyId) {
        match kind {
            Agg::Struct(_) => {
                let offs = self.ty().field_offsets(t);
                let fts = self.p.types.field_tys(t);
                for (i, o) in ops.iter().enumerate() {
                    let v = self.operand(cx, body, o);
                    let p = self.gep(cx, dst, offs[i]);
                    self.store(cx, fts[i], v, &p);
                }
            }
            Agg::Variant(_, vi) => {
                let (_, el) = self.ty().enum_layout(t);
                cx.line(&format!("store i{} {}, ptr {}", el.tag_bits, vi, dst));
                let fts = self.p.types.variants(t).unwrap()[*vi as usize].fields.clone();
                for (i, o) in ops.iter().enumerate() {
                    let v = self.operand(cx, body, o);
                    let p = self.gep(cx, dst, el.fields[*vi as usize][i]);
                    self.store(cx, fts[i], v, &p);
                }
            }
            Agg::Array(_) => {
                let TyKind::Array(e, _) = self.p.types.kind(t).clone() else { panic!() };
                let es = self.size(e);
                for (i, o) in ops.iter().enumerate() {
                    let v = self.operand(cx, body, o);
                    let p = self.gep(cx, dst, i as u64 * es);
                    self.store(cx, e, v, &p);
                }
            }
            Agg::View(_) | Agg::Closure(_) => {
                let pv = self.operand(cx, body, &ops[0]);
                let pt = self.operand_ty(body, &ops[0]);
                let pv = self.imm(cx, pv, pt);
                cx.line(&format!("store ptr {}, ptr {}", pv, dst));
                let lv = self.operand(cx, body, &ops[1]);
                let lt = self.operand_ty(body, &ops[1]);
                let lv = self.imm(cx, lv, lt);
                let p2 = self.gep(cx, dst, 8);
                let llt = if matches!(kind, Agg::View(_)) { "i64" } else { "ptr" };
                cx.line(&format!("store {} {}, ptr {}", llt, lv, p2));
            }
        }
    }

    fn binop(&mut self, cx: &mut FnCx, op: Op, t: TyId, a: &str, b: &str) -> String {
        let lt = self.scalar(t);
        let r = cx.t();
        let kind = self.p.types.kind(t).clone();
        match kind {
            TyKind::Float(_) => {
                let inst = match op {
                    Op::Add => "fadd",
                    Op::Sub => "fsub",
                    Op::Mul => "fmul",
                    Op::Div => "fdiv",
                    Op::Rem => "frem",
                    Op::Eq => "fcmp oeq",
                    Op::Ne => "fcmp une",
                    Op::Lt => "fcmp olt",
                    Op::Le => "fcmp ole",
                    Op::Gt => "fcmp ogt",
                    Op::Ge => "fcmp oge",
                    _ => panic!("float op {:?}", op),
                };
                cx.line(&format!("{} = {} {} {}, {}", r, inst, lt, a, b));
                r
            }
            TyKind::Int(i) => {
                let s = i.signed;
                match op {
                    Op::Add | Op::Sub | Op::Mul if self.p.checked => {
                        let name = match op {
                            Op::Add => "add",
                            Op::Sub => "sub",
                            _ => "mul",
                        };
                        let f = format!("llvm.{}{}.with.overflow.{}", if s { "s" } else { "u" }, name, lt);
                        self.declare(&f, &format!("declare {{ {}, i1 }} @{}({}, {})", lt, f, lt, lt));
                        let pair = cx.t();
                        cx.line(&format!("{} = call {{ {}, i1 }} @{}({} {}, {} {})", pair, lt, f, lt, a, lt, b));
                        cx.line(&format!("{} = extractvalue {{ {}, i1 }} {}, 0", r, lt, pair));
                        let o = cx.t();
                        cx.line(&format!("{} = extractvalue {{ {}, i1 }} {}, 1", o, lt, pair));
                        self.check(cx, &o, true, "integer overflow");
                        r
                    }
                    Op::Add | Op::AddWrap => {
                        cx.line(&format!("{} = add {} {}, {}", r, lt, a, b));
                        r
                    }
                    Op::Sub | Op::SubWrap => {
                        cx.line(&format!("{} = sub {} {}, {}", r, lt, a, b));
                        r
                    }
                    Op::Mul | Op::MulWrap => {
                        cx.line(&format!("{} = mul {} {}, {}", r, lt, a, b));
                        r
                    }
                    Op::Div | Op::Rem => {
                        let z = cx.t();
                        cx.line(&format!("{} = icmp eq {} {}, 0", z, lt, b));
                        self.check(cx, &z, true, "division by zero");
                        if s {
                            // MIN / -1 wraps to MIN, and MIN % -1 is 0.
                            let m1 = cx.t();
                            cx.line(&format!("{} = icmp eq {} {}, -1", m1, lt, b));
                            let safe_b = cx.t();
                            cx.line(&format!("{} = select i1 {}, {} 1, {} {}", safe_b, m1, lt, lt, b));
                            let q = cx.t();
                            cx.line(&format!("{} = {} {} {}, {}", q, if op == Op::Div { "sdiv" } else { "srem" }, lt, a, safe_b));
                            let alt = cx.t();
                            if op == Op::Div {
                                cx.line(&format!("{} = sub {} 0, {}", alt, lt, a));
                            } else {
                                cx.line(&format!("{} = add {} 0, 0", alt, lt));
                            }
                            cx.line(&format!("{} = select i1 {}, {} {}, {} {}", r, m1, lt, alt, lt, q));
                        } else {
                            cx.line(&format!("{} = {} {} {}, {}", r, if op == Op::Div { "udiv" } else { "urem" }, lt, a, b));
                        }
                        r
                    }
                    Op::And => {
                        cx.line(&format!("{} = and {} {}, {}", r, lt, a, b));
                        r
                    }
                    Op::Or => {
                        cx.line(&format!("{} = or {} {}, {}", r, lt, a, b));
                        r
                    }
                    Op::Xor => {
                        cx.line(&format!("{} = xor {} {}, {}", r, lt, a, b));
                        r
                    }
                    Op::Shl | Op::Shr => {
                        let m = cx.t();
                        cx.line(&format!("{} = and {} {}, {}", m, lt, b, i.bits - 1));
                        let inst = if op == Op::Shl { "shl" } else if s { "ashr" } else { "lshr" };
                        cx.line(&format!("{} = {} {} {}, {}", r, inst, lt, a, m));
                        r
                    }
                    Op::Eq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge => {
                        let c = icmp(op, s);
                        cx.line(&format!("{} = icmp {} {} {}, {}", r, c, lt, a, b));
                        r
                    }
                    Op::LogAnd | Op::LogOr => panic!("logic op in codegen"),
                }
            }
            TyKind::Bool => {
                let inst = match op {
                    Op::Eq => "icmp eq",
                    Op::Ne | Op::Xor => "icmp ne",
                    Op::And | Op::LogAnd => "and",
                    Op::Or | Op::LogOr => "or",
                    _ => panic!("bool op"),
                };
                cx.line(&format!("{} = {} i1 {}, {}", r, inst, a, b));
                r
            }
            _ => {
                // Pointers and function pointers: comparisons.
                let c = icmp(op, false);
                cx.line(&format!("{} = icmp {} ptr {}, {}", r, c, a, b));
                r
            }
        }
    }

    /// Stops the program with a message when `cond` is `bad`.
    fn check(&mut self, cx: &mut FnCx, cond: &str, bad: bool, msg: &str) {
        let id = cx.t().replace('%', "");
        let (ok, fail) = (format!("{}.ok", id), format!("{}.fail", id));
        if bad {
            cx.line(&format!("br i1 {}, label %{}, label %{}", cond, fail, ok));
        } else {
            cx.line(&format!("br i1 {}, label %{}, label %{}", cond, ok, fail));
        }
        cx.body.push_str(&format!("{}:\n", fail));
        self.panic_msg(cx, msg);
        cx.body.push_str(&format!("{}:\n", ok));
        cx.set_block(&ok);
    }

    fn cast(&mut self, cx: &mut FnCx, v: &str, from: TyId, to: TyId) -> String {
        let fk = self.p.types.kind(from).clone();
        let tk = self.p.types.kind(to).clone();
        let ft = self.scalar(from);
        let tt = self.scalar(to);
        let r = cx.t();
        match (fk, tk) {
            (TyKind::Int(a), TyKind::Int(b)) => {
                if a.bits == b.bits {
                    return v.to_string();
                }
                let inst = if b.bits < a.bits {
                    "trunc"
                } else if a.signed {
                    "sext"
                } else {
                    "zext"
                };
                cx.line(&format!("{} = {} {} {} to {}", r, inst, ft, v, tt));
            }
            (TyKind::Bool, TyKind::Int(_)) => cx.line(&format!("{} = zext i1 {} to {}", r, v, tt)),
            (TyKind::Int(a), TyKind::Float(_)) => {
                cx.line(&format!("{} = {} {} {} to {}", r, if a.signed { "sitofp" } else { "uitofp" }, ft, v, tt))
            }
            (TyKind::Float(_), TyKind::Int(b)) => {
                // Saturating: NaN is 0, out of range is the nearest end.
                let f = format!("llvm.fpto{}i.sat.{}.{}", if b.signed { "s" } else { "u" }, tt, ft);
                self.declare(&f, &format!("declare {} @{}({})", tt, f, ft));
                cx.line(&format!("{} = call {} @{}({} {})", r, tt, f, ft, v));
            }
            (TyKind::Float(a), TyKind::Float(b)) => {
                if a == b {
                    return v.to_string();
                }
                cx.line(&format!("{} = {} {} {} to {}", r, if b > a { "fpext" } else { "fptrunc" }, ft, v, tt));
            }
            (TyKind::Int(_), _) if tt == "ptr" => cx.line(&format!("{} = inttoptr {} {} to ptr", r, ft, v)),
            (_, TyKind::Int(_)) if ft == "ptr" => cx.line(&format!("{} = ptrtoint ptr {} to {}", r, v, tt)),
            _ => return v.to_string(),
        }
        r
    }

    fn term(&mut self, cx: &mut FnCx, f: FnId, body: &Body, t: &Term) {
        match t {
            Term::Goto(b) => cx.line(&format!("br label %bb{}", b)),
            Term::Switch { discr, targets, otherwise } => {
                let dt = self.operand_ty(body, discr);
                let dv = self.operand(cx, body, discr);
                let dv = self.imm(cx, dv, dt);
                let lt = self.scalar(dt);
                if dt == types::BOOL && targets.len() == 1 && targets[0].0 == 0 {
                    cx.line(&format!("br i1 {}, label %bb{}, label %bb{}", dv, otherwise, targets[0].1));
                    return;
                }
                let mut cases = String::new();
                for (v, b) in targets {
                    let v = if dt == types::BOOL { (*v != 0).to_string() } else { v.to_string() };
                    let _ = write!(cases, " {} {}, label %bb{}", lt, v, b);
                }
                cx.line(&format!("switch {} {}, label %bb{} [{} ]", lt, dv, otherwise, cases));
            }
            Term::Return => {
                let ret = self.p.fns[f as usize].sig.ret;
                if cx.sret.is_some() || ret == types::NEVER || self.ty().is_zst(ret) {
                    cx.line("ret void");
                } else {
                    let p = cx.locals[0].clone();
                    let v = self.load_scalar(cx, ret, &p);
                    let lt = self.scalar(ret);
                    cx.line(&format!("ret {} {}", lt, v));
                }
            }
            Term::Unreachable | Term::Pending => cx.line("unreachable"),
            Term::Assert { cond, msg, next, .. } => {
                let ct = self.operand_ty(body, cond);
                let cv = self.operand(cx, body, cond);
                let cv = self.imm(cx, cv, ct);
                let id = cx.t().replace('%', "");
                cx.line(&format!("br i1 {}, label %bb{}, label %{}.fail", cv, next, id));
                cx.body.push_str(&format!("{}.fail:\n", id));
                self.panic_msg(cx, msg);
            }
            Term::Call { callee, args, dest, next, .. } => {
                self.call(cx, body, callee, args, dest);
                cx.line(&format!("br label %bb{}", next));
            }
        }
    }

    fn call(&mut self, cx: &mut FnCx, body: &Body, callee: &Callee, args: &[Operand], dest: &Place) {
        let (dptr, dt) = self.place(cx, body, dest);
        let (sig, pass, target, c_abi, variadic) = match callee {
            Callee::Fn(f) => {
                let fun = self.p.fns[*f as usize].clone();
                let c = fun.linkage != Linkage::Internal;
                (fun.sig.clone(), fun.pass.clone(), sym(&fun.symbol), c, fun.variadic)
            }
            Callee::Ptr(o) => {
                let ot = self.operand_ty(body, o);
                let TyKind::FnPtr(sig) = self.p.types.kind(ot).clone() else { panic!() };
                let v = self.operand(cx, body, o);
                let fp = self.imm(cx, v, ot);
                let pass = sig.params.iter().map(|&t| if self.p.types.is_ref(t) { ParamPass::Borrow } else { ParamPass::Value }).collect();
                (sig, pass, fp, false, false)
            }
            Callee::Closure(o) => {
                let ot = self.operand_ty(body, o);
                let TyKind::Closure(sig) = self.p.types.kind(ot).clone() else { panic!() };
                let (Operand::Copy(cp) | Operand::Move(cp)) = o else { panic!("closure constant") };
                let (cptr, _) = self.place(cx, body, cp);
                let fp = cx.t();
                cx.line(&format!("{} = load ptr, ptr {}", fp, cptr));
                let ep = self.gep(cx, &cptr, 8);
                let env = cx.t();
                cx.line(&format!("{} = load ptr, ptr {}", env, ep));
                let mut params = vec![self.ty().ptr(types::U8)];
                params.extend(sig.params.iter().copied());
                let mut pass = vec![ParamPass::Value];
                pass.extend(sig.params.iter().map(|&t| if self.p.types.is_ref(t) { ParamPass::Borrow } else { ParamPass::Value }));
                let s2 = types::Sig { params, ret: sig.ret };
                // The environment goes first.
                return self.emit_call_inst(cx, body, &s2, &pass, &fp, false, false, Some(env), args, &dptr, dt);
            }
            Callee::Intrinsic(i) => {
                self.intrinsic(cx, body, i, args, &dptr, dt);
                return;
            }
        };
        self.emit_call_inst(cx, body, &sig, &pass, &target, c_abi, variadic, None, args, &dptr, dt);
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_call_inst(
        &mut self,
        cx: &mut FnCx,
        body: &Body,
        sig: &types::Sig,
        pass: &[ParamPass],
        target: &str,
        c_abi: bool,
        variadic: bool,
        env: Option<String>,
        args: &[Operand],
        dptr: &str,
        dt: TyId,
    ) {
        let ret = sig.ret;
        let mut actual = Vec::new();
        let sret = ret != types::NEVER && !self.ty().is_zst(ret) && !self.is_scalar(ret);
        if sret {
            actual.push(format!("ptr {}", dptr));
        }
        let mut pi = 0;
        let mut param_tys: Vec<String> = Vec::new();
        if sret {
            param_tys.push("ptr".into());
        }
        if let Some(e) = env {
            actual.push(format!("ptr {}", e));
            param_tys.push("ptr".into());
            pi = 1;
        }
        for (ai, o) in args.iter().enumerate() {
            let idx = ai + pi;
            let pt = sig.params.get(idx).copied().unwrap_or_else(|| self.operand_ty(body, o));
            let pp = pass.get(idx).copied().unwrap_or(ParamPass::Value);
            let v = self.operand(cx, body, o);
            if self.is_scalar(pt) {
                let x = self.imm(cx, v, pt);
                let ty = if c_abi && pt == types::BOOL { "zeroext i1".to_string() } else { self.scalar(pt) };
                actual.push(format!("{} {}", ty, x));
                param_tys.push(ty);
            } else {
                // Aggregates by pointer; a callee that owns the value gets
                // its own copy unless the value was moved.
                let p = match (v, pp, o) {
                    (V::Mem(m), ParamPass::Owned, Operand::Move(_)) => m,
                    (V::Mem(m), ParamPass::Value, _) => m,
                    (v, _, _) => {
                        let s = self.size(pt).max(1);
                        let a = self.align(pt);
                        let tmp = cx.t();
                        cx.line(&format!("{} = alloca [{} x i8], align {}", tmp, s, a));
                        self.store(cx, pt, v, &tmp);
                        tmp
                    }
                };
                actual.push(format!("ptr {}", p));
                param_tys.push("ptr".into());
            }
        }
        let rty = if ret == types::NEVER || self.ty().is_zst(ret) || sret {
            "void".to_string()
        } else if c_abi && ret == types::BOOL {
            "zeroext i1".to_string()
        } else {
            self.scalar(ret)
        };
        let fnty = if variadic {
            let fixed: Vec<String> = param_tys.iter().take(sig.params.len() + sret as usize).cloned().collect();
            format!("{} ({}, ...)", rty, fixed.join(", "))
        } else {
            rty.clone()
        };
        if rty == "void" {
            cx.line(&format!("call {} {}({})", fnty, target, actual.join(", ")));
        } else {
            let r = cx.t();
            cx.line(&format!("{} = call {} {}({})", r, fnty, target, actual.join(", ")));
            self.store_scalar(cx, dt, &r, dptr);
        }
        if ret == types::NEVER {
            cx.line("unreachable");
            let id = cx.t().replace('%', "");
            cx.body.push_str(&format!("{}.dead:\n", id));
        }
    }

    fn intrinsic(&mut self, cx: &mut FnCx, body: &Body, i: &Intrinsic, args: &[Operand], dptr: &str, dt: TyId) {
        let mut vals = Vec::new();
        let mut tys = Vec::new();
        for o in args {
            let t = self.operand_ty(body, o);
            let v = self.operand(cx, body, o);
            let x = if self.is_scalar(t) { self.imm(cx, v, t) } else { String::new() };
            vals.push(x);
            tys.push(t);
        }
        match i {
            Intrinsic::Trap => {
                cx.line("call void @llvm.trap()");
                cx.line("unreachable");
                let id = cx.t().replace('%', "");
                cx.body.push_str(&format!("{}.dead:\n", id));
            }
            Intrinsic::Syscall => {
                let n = vals.len();
                let (asm, cons) = syscall_asm(self.p.target, n);
                let argl: Vec<String> = vals.iter().map(|v| format!("i64 {}", v)).collect();
                let r = cx.t();
                cx.line(&format!("{} = call i64 asm sideeffect \"{}\", \"{}\"({})", r, asm, cons, argl.join(", ")));
                self.store_scalar(cx, dt, &r, dptr);
            }
            Intrinsic::Copy(e) => {
                let es = self.size(*e);
                let n = cx.t();
                cx.line(&format!("{} = mul i64 {}, {}", n, vals[2], es));
                cx.line(&format!("call void @llvm.memmove.p0.p0.i64(ptr {}, ptr {}, i64 {}, i1 false)", vals[0], vals[1], n));
            }
            Intrinsic::Fill => {
                cx.line(&format!("call void @llvm.memset.p0.i64(ptr {}, i8 {}, i64 {}, i1 false)", vals[0], vals[1], vals[2]));
            }
            Intrinsic::Sqrt(t) | Intrinsic::Floor(t) | Intrinsic::Ceil(t) | Intrinsic::Trunc(t) | Intrinsic::Round(t) | Intrinsic::Abs(t) => {
                let lt = self.scalar(*t);
                let r = cx.t();
                if self.p.types.is_int(*t) {
                    let f = format!("llvm.abs.{}", lt);
                    self.declare(&f, &format!("declare {} @{}({}, i1)", lt, f, lt));
                    cx.line(&format!("{} = call {} @{}({} {}, i1 false)", r, lt, f, lt, vals[0]));
                } else {
                    let name = match i {
                        Intrinsic::Sqrt(_) => "sqrt",
                        Intrinsic::Floor(_) => "floor",
                        Intrinsic::Ceil(_) => "ceil",
                        Intrinsic::Trunc(_) => "trunc",
                        Intrinsic::Round(_) => "round",
                        _ => "fabs",
                    };
                    let suffix = if lt == "float" { "f32" } else { "f64" };
                    let f = format!("llvm.{}.{}", name, suffix);
                    self.declare(&f, &format!("declare {} @{}({})", lt, f, lt));
                    cx.line(&format!("{} = call {} @{}({} {})", r, lt, f, lt, vals[0]));
                }
                self.store_scalar(cx, dt, &r, dptr);
            }
            Intrinsic::Copysign(t) => {
                let lt = self.scalar(*t);
                let suffix = if lt == "float" { "f32" } else { "f64" };
                let f = format!("llvm.copysign.{}", suffix);
                self.declare(&f, &format!("declare {} @{}({}, {})", lt, f, lt, lt));
                let r = cx.t();
                cx.line(&format!("{} = call {} @{}({} {}, {} {})", r, lt, f, lt, vals[0], lt, vals[1]));
                self.store_scalar(cx, dt, &r, dptr);
            }
            Intrinsic::Argc => {
                let r = cx.t();
                cx.line(&format!("{} = load i64, ptr @jihoo.argc", r));
                self.store_scalar(cx, dt, &r, dptr);
            }
            Intrinsic::Argv => {
                let r = cx.t();
                cx.line(&format!("{} = load ptr, ptr @jihoo.argv", r));
                self.store_scalar(cx, dt, &r, dptr);
            }
            Intrinsic::AtomicLoad(t) => {
                let lt = self.mem_scalar(*t);
                let a = self.align(*t);
                let r = cx.t();
                cx.line(&format!("{} = load atomic {}, ptr {} seq_cst, align {}", r, lt, vals[0], a));
                let r = if *t == types::BOOL {
                    let b = cx.t();
                    cx.line(&format!("{} = trunc i8 {} to i1", b, r));
                    b
                } else {
                    r
                };
                self.store_scalar(cx, dt, &r, dptr);
            }
            Intrinsic::AtomicStore(t) => {
                let lt = self.mem_scalar(*t);
                let a = self.align(*t);
                let v = self.widen_bool(cx, *t, &vals[1]);
                cx.line(&format!("store atomic {} {}, ptr {} seq_cst, align {}", lt, v, vals[0], a));
            }
            Intrinsic::AtomicRmw(op, t) => {
                let lt = self.mem_scalar(*t);
                let v = self.widen_bool(cx, *t, &vals[1]);
                let r = cx.t();
                let op = match op.as_str() {
                    "swap" => "xchg",
                    o => o,
                };
                cx.line(&format!("{} = atomicrmw {} ptr {}, {} {} seq_cst", r, op, vals[0], lt, v));
                let r = if *t == types::BOOL {
                    let b = cx.t();
                    cx.line(&format!("{} = trunc i8 {} to i1", b, r));
                    b
                } else {
                    r
                };
                self.store_scalar(cx, dt, &r, dptr);
            }
            Intrinsic::AtomicCas(t) => {
                let lt = self.mem_scalar(*t);
                let e = self.widen_bool(cx, *t, &vals[1]);
                let n = self.widen_bool(cx, *t, &vals[2]);
                let pair = cx.t();
                cx.line(&format!("{} = cmpxchg ptr {}, {} {}, {} {} seq_cst seq_cst", pair, vals[0], lt, e, lt, n));
                let r = cx.t();
                cx.line(&format!("{} = extractvalue {{ {}, i1 }} {}, 1", r, lt, pair));
                self.store_scalar(cx, dt, &r, dptr);
            }
            Intrinsic::Fence => cx.line("fence seq_cst"),
            Intrinsic::Asm(..) => {}
        }
    }

    fn widen_bool(&mut self, cx: &mut FnCx, t: TyId, v: &str) -> String {
        if t != types::BOOL {
            return v.to_string();
        }
        let r = cx.t();
        cx.line(&format!("{} = zext i1 {} to i8", r, v));
        r
    }

    // ---- the program's entry and runtime pieces ----

    fn entry(&mut self) {
        let Some(main) = self.p.entry else { return };
        let fun = self.p.fns[main as usize].clone();
        let ret = fun.sig.ret;
        // Calls main and leaves its exit status, as an i32, in %code.
        let mut call = String::new();
        if self.ty().is_zst(ret) || ret == types::NEVER {
            let _ = writeln!(call, "  call void {}()", sym(&fun.symbol));
            call.push_str("  %code = add i32 0, 0\n");
        } else {
            let lt = self.scalar(ret);
            let _ = writeln!(call, "  %r = call {} {}()", lt, sym(&fun.symbol));
            let conv = match self.p.types.kind(ret) {
                TyKind::Int(i) if i.bits == 32 => "%code = add i32 %r, 0".to_string(),
                TyKind::Int(i) if i.bits > 32 => format!("%code = trunc {} %r to i32", lt),
                TyKind::Int(i) => format!("%code = {} {} %r to i32", if i.signed { "sext" } else { "zext" }, lt),
                TyKind::Bool => "%code = zext i1 %r to i32".to_string(),
                _ => "%code = add i32 0, 0".to_string(),
            };
            let _ = writeln!(call, "  {}", conv);
        }
        if self.p.freestanding {
            // `_start`: the stack holds argc, then argv.
            let _ = writeln!(self.out, "module asm \"{}\"\n", start_asm(self.p.target));
            let (exit_asm, cons) = syscall_asm(self.p.target, 2);
            let exit_no = match self.p.target {
                Target::X86_64 => 231,
                Target::Aarch64 => 94,
            };
            let _ = writeln!(
                self.out,
                "define void @jihoo.start(ptr %sp) {{\nentry:\n  %argc = load i64, ptr %sp\n  store i64 %argc, ptr @jihoo.argc\n  %argv = getelementptr i8, ptr %sp, i64 8\n  store ptr %argv, ptr @jihoo.argv\n{}  %c64 = sext i32 %code to i64\n  %x = call i64 asm sideeffect \"{}\", \"{}\"(i64 {}, i64 %c64)\n  unreachable\n}}\n",
                call, exit_asm, cons, exit_no
            );
            self.mem_functions();
        } else {
            let _ = writeln!(
                self.out,
                "define i32 @main(i32 %argc, ptr %argv) {{\nentry:\n  %a = sext i32 %argc to i64\n  store i64 %a, ptr @jihoo.argc\n  store ptr %argv, ptr @jihoo.argv\n{}  ret i32 %code\n}}\n",
                call
            );
        }
    }

    /// Without libc, LLVM's calls to `memcpy` and friends need definitions;
    /// "no-builtins" keeps LLVM from turning their loops back into calls.
    fn mem_functions(&mut self) {
        self.out.push_str(
            r#"define weak ptr @memcpy(ptr %d, ptr %s, i64 %n) "no-builtins" {
entry:
  br label %head
head:
  %i = phi i64 [ 0, %entry ], [ %i1, %body ]
  %c = icmp ult i64 %i, %n
  br i1 %c, label %body, label %done
body:
  %sp = getelementptr i8, ptr %s, i64 %i
  %dp = getelementptr i8, ptr %d, i64 %i
  %b = load i8, ptr %sp
  store i8 %b, ptr %dp
  %i1 = add i64 %i, 1
  br label %head
done:
  ret ptr %d
}

define weak ptr @memmove(ptr %d, ptr %s, i64 %n) "no-builtins" {
entry:
  %fwd = icmp ule ptr %d, %s
  br i1 %fwd, label %f.head, label %b.head
f.head:
  %i = phi i64 [ 0, %entry ], [ %i1, %f.body ]
  %c = icmp ult i64 %i, %n
  br i1 %c, label %f.body, label %done
f.body:
  %sp = getelementptr i8, ptr %s, i64 %i
  %dp = getelementptr i8, ptr %d, i64 %i
  %b = load i8, ptr %sp
  store i8 %b, ptr %dp
  %i1 = add i64 %i, 1
  br label %f.head
b.head:
  %j = phi i64 [ %n, %entry ], [ %j1, %b.body ]
  %cj = icmp ugt i64 %j, 0
  br i1 %cj, label %b.body, label %done
b.body:
  %j1 = sub i64 %j, 1
  %sq = getelementptr i8, ptr %s, i64 %j1
  %dq = getelementptr i8, ptr %d, i64 %j1
  %bq = load i8, ptr %sq
  store i8 %bq, ptr %dq
  br label %b.head
done:
  ret ptr %d
}

define weak ptr @memset(ptr %d, i32 %v, i64 %n) "no-builtins" {
entry:
  %b = trunc i32 %v to i8
  br label %head
head:
  %i = phi i64 [ 0, %entry ], [ %i1, %body ]
  %c = icmp ult i64 %i, %n
  br i1 %c, label %body, label %done
body:
  %dp = getelementptr i8, ptr %d, i64 %i
  store i8 %b, ptr %dp
  %i1 = add i64 %i, 1
  br label %head
done:
  ret ptr %d
}

define weak i32 @memcmp(ptr %a, ptr %b, i64 %n) "no-builtins" {
entry:
  br label %head
head:
  %i = phi i64 [ 0, %entry ], [ %i1, %next ]
  %c = icmp ult i64 %i, %n
  br i1 %c, label %body, label %same
body:
  %ap = getelementptr i8, ptr %a, i64 %i
  %bp = getelementptr i8, ptr %b, i64 %i
  %x = load i8, ptr %ap
  %y = load i8, ptr %bp
  %eq = icmp eq i8 %x, %y
  br i1 %eq, label %next, label %diff
next:
  %i1 = add i64 %i, 1
  br label %head
diff:
  %xz = zext i8 %x to i32
  %yz = zext i8 %y to i32
  %d = sub i32 %xz, %yz
  ret i32 %d
same:
  ret i32 0
}

"#,
        );
    }

    /// `jihoo.panic(msg, len)`: writes the message to standard error and
    /// stops. Uses the system call directly, so it works without libc.
    fn runtime(&mut self) {
        let (wasm, wcons) = syscall_asm(self.p.target, 4);
        let (prefix, plen) = self.str_global(b"panic: ");
        let (nl, _) = self.str_global(b"\n");
        let write_no = match self.p.target {
            Target::X86_64 => 1,
            Target::Aarch64 => 64,
        };
        let _ = writeln!(
            self.out,
            "define internal void @jihoo.panic(ptr %m, i64 %n) cold noreturn {{\nentry:\n  %a = call i64 asm sideeffect \"{w}\", \"{c}\"(i64 {no}, i64 2, ptr {p}, i64 {pl})\n  %b = call i64 asm sideeffect \"{w}\", \"{c}\"(i64 {no}, i64 2, ptr %m, i64 %n)\n  %d = call i64 asm sideeffect \"{w}\", \"{c}\"(i64 {no}, i64 2, ptr {nl}, i64 1)\n  call void @llvm.trap()\n  unreachable\n}}\n",
            w = wasm,
            c = wcons,
            no = write_no,
            p = prefix,
            pl = plen,
            nl = nl
        );
        for d in [
            "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)",
            "declare void @llvm.memmove.p0.p0.i64(ptr, ptr, i64, i1)",
            "declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)",
            "declare void @llvm.trap() cold noreturn nounwind",
        ] {
            let name = d.split('@').nth(1).unwrap().split('(').next().unwrap().to_string();
            self.declare(&name, d);
        }
    }
}

impl FnCx {
    /// The label of the block being written (for phis).
    fn label_block(&self) -> String {
        let mut last = "entry".to_string();
        for line in self.body.lines() {
            if !line.starts_with(' ') && line.ends_with(':') {
                last = line.trim_end_matches(':').to_string();
            }
        }
        last
    }
    fn set_block(&mut self, _l: &str) {}
}

fn icmp(op: Op, signed: bool) -> &'static str {
    match (op, signed) {
        (Op::Eq, _) => "eq",
        (Op::Ne, _) => "ne",
        (Op::Lt, true) => "slt",
        (Op::Le, true) => "sle",
        (Op::Gt, true) => "sgt",
        (Op::Ge, true) => "sge",
        (Op::Lt, false) => "ult",
        (Op::Le, false) => "ule",
        (Op::Gt, false) => "ugt",
        (Op::Ge, false) => "uge",
        _ => panic!("not a comparison"),
    }
}

/// Inline assembly for a system call with `n` operands (the number first).
fn syscall_asm(t: Target, n: usize) -> (String, String) {
    match t {
        Target::X86_64 => {
            let regs = ["{rax}", "{rdi}", "{rsi}", "{rdx}", "{r10}", "{r8}", "{r9}"];
            let ins: Vec<&str> = regs[..n].to_vec();
            ("syscall".into(), format!("={{rax}},{},~{{rcx}},~{{r11}},~{{memory}}", ins.join(",")))
        }
        Target::Aarch64 => {
            let regs = ["{x8}", "{x0}", "{x1}", "{x2}", "{x3}", "{x4}", "{x5}"];
            let ins: Vec<&str> = regs[..n].to_vec();
            ("svc #0".into(), format!("={{x0}},{},~{{memory}}", ins.join(",")))
        }
    }
}

fn start_asm(t: Target) -> &'static str {
    match t {
        Target::X86_64 => ".globl _start\\0A_start:\\0A  xor %rbp, %rbp\\0A  mov %rsp, %rdi\\0A  and $-16, %rsp\\0A  call jihoo.start\\0A  hlt\\0A",
        Target::Aarch64 => ".globl _start\\0A_start:\\0A  mov x29, #0\\0A  mov x30, #0\\0A  mov x0, sp\\0A  bl jihoo.start\\0A  brk #0\\0A",
    }
}
