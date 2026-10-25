// MIR: what sema produces and the checker, the interpreter and the code
// generator read. A function is a control-flow graph over places; every
// move, copy, borrow and drop is explicit.

use crate::diag::Span;
use crate::lex::Op;
use crate::types::{Sig, TyId, Types};

pub type Local = u32;
pub type BlockId = u32;
pub type FnId = u32;

pub const RET: Local = 0;

#[derive(Clone, Debug, PartialEq)]
pub enum Proj {
    Field(u32),
    /// The payload of a variant, followed by a `Field`.
    Variant(u32),
    /// An array element; sema checks the bounds before.
    Index(Local),
    Deref,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Place {
    pub local: Local,
    pub proj: Vec<Proj>,
}

impl Place {
    pub fn local(l: Local) -> Place {
        Place { local: l, proj: Vec::new() }
    }
    pub fn with(&self, p: Proj) -> Place {
        let mut q = self.clone();
        q.proj.push(p);
        q
    }
    pub fn deref(l: Local) -> Place {
        Place { local: l, proj: vec![Proj::Deref] }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Const {
    /// The bits of an integer of the given type, sign-extended.
    Int(i128, TyId),
    Float(f64, TyId),
    Bool(bool),
    /// A value without bytes: `()`, a struct without fields.
    Zst(TyId),
    /// A `str` of static bytes.
    Str(Vec<u8>),
    /// A function's address (`fnptr`).
    Fn(FnId),
    Null(TyId),
    /// All bits zero.
    Zeroed(TyId),
    /// Static bytes, laid out as the type says (compile-time results).
    Bytes(Vec<u8>, TyId),
    /// The address of a `static`.
    Static(u32, TyId),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Const(Const),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Agg {
    /// A struct or tuple, its fields in order.
    Struct(TyId),
    Variant(TyId, u32),
    Array(TyId),
    /// A `str` or slice from a pointer and a length.
    View(TyId),
    /// A closure from a function and an environment pointer.
    Closure(TyId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CastKind {
    /// Between integers, floats, pointers and integers.
    Numeric,
    /// A pointer to another pointer type, a borrow to a pointer.
    Ptr,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Rvalue {
    Use(Operand),
    /// Arithmetic that checks for overflow when `checked`.
    Bin(Op, Operand, Operand),
    Un(UnOp, Operand),
    Cast(Operand, TyId, CastKind),
    Ref(Place),
    RefMut(Place),
    /// The address of a place, as a raw pointer.
    Addr(Place),
    Aggregate(Agg, Vec<Operand>),
    Discriminant(Place),
    /// A pointer moved by a number of elements.
    Offset(Operand, Operand),
    /// An array of `n` copies of a plain value.
    Repeat(Operand, u64),
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Assign(Place, Rvalue, Span),
    StorageLive(Local),
    StorageDead(Local),
    /// Runs the value's destructor; drop elaboration removes the ones whose
    /// value was moved away.
    Drop(Place, Span),
    /// The local's value is gone: its parts were moved out or dropped one
    /// by one.
    Forget(Local),
    Nop,
}

#[derive(Clone, Debug)]
pub enum Callee {
    Fn(FnId),
    /// A `fnptr` value.
    Ptr(Operand),
    /// A `fn(A) -> R` value: its environment is passed first.
    Closure(Operand),
    Intrinsic(Intrinsic),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Intrinsic {
    Trap,
    /// `syscall(n, args...)`.
    Syscall,
    /// Copies `n` elements from the second pointer to the first (memmove).
    Copy(TyId),
    /// Fills `n` bytes at a pointer with a byte.
    Fill,
    Sqrt(TyId),
    Floor(TyId),
    Ceil(TyId),
    Trunc(TyId),
    Round(TyId),
    Abs(TyId),
    Copysign(TyId),
    /// Inline assembly: template, constraints, result type.
    Asm(String, String, TyId),
    AtomicLoad(TyId),
    AtomicStore(TyId),
    AtomicRmw(String, TyId),
    AtomicCas(TyId),
    Fence,
    /// `args()` support: the C `argc`/`argv` kept by `main`.
    Argc,
    Argv,
}

#[derive(Clone, Debug)]
pub enum Term {
    Goto(BlockId),
    /// Jumps on an integer, bool or tag value.
    Switch { discr: Operand, targets: Vec<(i128, BlockId)>, otherwise: BlockId },
    Return,
    Unreachable,
    Call { callee: Callee, args: Vec<Operand>, dest: Place, next: BlockId, span: Span },
    /// Continues to `next` when `cond` holds, else stops the program with
    /// the message.
    Assert { cond: Operand, msg: String, next: BlockId, span: Span },
    /// Not filled in yet (while building).
    Pending,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub term: Term,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalKind {
    Ret,
    Arg,
    Var,
    Temp,
}

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub ty: TyId,
    pub name: Option<String>,
    pub span: Span,
    pub mutable: bool,
    pub kind: LocalKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamPass {
    /// By value (scalars, and small plain values read only).
    Value,
    /// A pointer to a value the function owns (`sink` aggregates).
    Owned,
    /// A borrow; the local's type is `Ref`/`RefMut`.
    Borrow,
}

#[derive(Clone, Debug)]
pub struct Body {
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<Block>,
    pub arg_count: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Linkage {
    Internal,
    /// `export fn` and `main`: visible to the linker under its own name.
    Export,
    /// `extern fn`: defined elsewhere, called with the C convention.
    Extern,
}

#[derive(Clone, Debug)]
pub struct Function {
    /// The symbol: unique, mangled for instances.
    pub symbol: String,
    /// What error messages and MIR dumps call it.
    pub name: String,
    pub sig: Sig,
    /// Per parameter: how it is passed.
    pub pass: Vec<ParamPass>,
    pub body: Option<Body>,
    pub linkage: Linkage,
    pub variadic: bool,
    /// The function returns a borrow of its first parameter.
    pub returns_ref: bool,
    /// Calls to it are in tail position and must not grow the stack.
    pub span: Span,
}

pub struct Program {
    pub fns: Vec<Function>,
    pub types: Types,
    pub entry: Option<FnId>,
    pub freestanding: bool,
    /// Integer overflow traps (debug builds).
    pub checked: bool,
    /// Global variables: symbol, type, first value.
    pub statics: Vec<(String, TyId, Const)>,
    /// The `drop` function of each type with a `Drop` impl.
    pub drop_impls: std::collections::HashMap<TyId, FnId>,
    pub target: crate::target::Target,
}

// ---- printing ----

pub fn show_place(p: &Place) -> String {
    let mut s = format!("_{}", p.local);
    for pr in &p.proj {
        match pr {
            Proj::Field(i) => s = format!("{}.{}", s, i),
            Proj::Variant(v) => s = format!("({} as #{})", s, v),
            Proj::Index(l) => s = format!("{}[_{}]", s, l),
            Proj::Deref => s = format!("(*{})", s),
        }
    }
    s
}

pub fn show_operand(t: &Types, o: &Operand) -> String {
    match o {
        Operand::Copy(p) => show_place(p),
        Operand::Move(p) => format!("move {}", show_place(p)),
        Operand::Const(c) => match c {
            Const::Int(v, ty) => format!("{}_{}", v, t.show(*ty)),
            Const::Float(v, ty) => format!("{}_{}", v, t.show(*ty)),
            Const::Bool(b) => b.to_string(),
            Const::Zst(_) => "()".into(),
            Const::Str(s) => format!("{:?}", String::from_utf8_lossy(s)),
            Const::Fn(f) => format!("fn#{}", f),
            Const::Null(_) => "null".into(),
            Const::Zeroed(ty) => format!("zeroed({})", t.show(*ty)),
            Const::Bytes(b, ty) => format!("bytes[{}]({})", b.len(), t.show(*ty)),
            Const::Static(i, _) => format!("static#{}", i),
        },
    }
}

pub fn show_rvalue(t: &Types, r: &Rvalue) -> String {
    let ops = |os: &[Operand]| os.iter().map(|o| show_operand(t, o)).collect::<Vec<_>>().join(", ");
    match r {
        Rvalue::Use(o) => show_operand(t, o),
        Rvalue::Bin(op, a, b) => format!("{} {} {}", show_operand(t, a), op.text(), show_operand(t, b)),
        Rvalue::Un(UnOp::Neg, a) => format!("-{}", show_operand(t, a)),
        Rvalue::Un(UnOp::Not, a) => format!("!{}", show_operand(t, a)),
        Rvalue::Cast(a, ty, _) => format!("{} as {}", show_operand(t, a), t.show(*ty)),
        Rvalue::Ref(p) => format!("&{}", show_place(p)),
        Rvalue::RefMut(p) => format!("&mut {}", show_place(p)),
        Rvalue::Addr(p) => format!("addr {}", show_place(p)),
        Rvalue::Aggregate(a, os) => match a {
            Agg::Struct(ty) => format!("{} {{ {} }}", t.show(*ty), ops(os)),
            Agg::Variant(ty, v) => format!("{}#{}({})", t.show(*ty), v, ops(os)),
            Agg::Array(_) => format!("[{}]", ops(os)),
            Agg::View(ty) => format!("{}({})", t.show(*ty), ops(os)),
            Agg::Closure(_) => format!("closure({})", ops(os)),
        },
        Rvalue::Discriminant(p) => format!("discr {}", show_place(p)),
        Rvalue::Offset(a, b) => format!("offset {}, {}", show_operand(t, a), show_operand(t, b)),
        Rvalue::Repeat(a, n) => format!("[{}; {}]", show_operand(t, a), n),
    }
}

pub fn show_function(p: &Program, f: &Function) -> String {
    let t = &p.types;
    let mut s = format!("fn {} [{}]", f.name, f.symbol);
    let Some(b) = &f.body else {
        return s + " (extern)\n";
    };
    s.push_str(" {\n");
    for (i, l) in b.locals.iter().enumerate() {
        s.push_str(&format!(
            "  let {}_{}: {}{}\n",
            if l.mutable { "mut " } else { "" },
            i,
            t.show(l.ty),
            l.name.as_ref().map(|n| format!("  // {}", n)).unwrap_or_default()
        ));
    }
    for (i, blk) in b.blocks.iter().enumerate() {
        s.push_str(&format!(" bb{}:\n", i));
        for st in &blk.stmts {
            match st {
                Stmt::Assign(pl, r, _) => s.push_str(&format!("    {} = {}\n", show_place(pl), show_rvalue(t, r))),
                Stmt::StorageLive(l) => s.push_str(&format!("    live _{}\n", l)),
                Stmt::StorageDead(l) => s.push_str(&format!("    dead _{}\n", l)),
                Stmt::Drop(pl, _) => s.push_str(&format!("    drop {}\n", show_place(pl))),
                Stmt::Forget(l) => s.push_str(&format!("    forget _{}\n", l)),
                Stmt::Nop => {}
            }
        }
        let term = match &blk.term {
            Term::Goto(b) => format!("goto bb{}", b),
            Term::Switch { discr, targets, otherwise } => {
                let ts: Vec<String> = targets.iter().map(|(v, b)| format!("{} => bb{}", v, b)).collect();
                format!("switch {} [{}; else bb{}]", show_operand(t, discr), ts.join(", "), otherwise)
            }
            Term::Return => "return".into(),
            Term::Unreachable => "unreachable".into(),
            Term::Call { callee, args, dest, next, .. } => {
                let c = match callee {
                    Callee::Fn(f) => p.fns[*f as usize].name.clone(),
                    Callee::Ptr(o) | Callee::Closure(o) => show_operand(t, o),
                    Callee::Intrinsic(i) => format!("{:?}", i),
                };
                let a: Vec<String> = args.iter().map(|o| show_operand(t, o)).collect();
                format!("{} = call {}({}) -> bb{}", show_place(dest), c, a.join(", "), next)
            }
            Term::Assert { cond, msg, next, .. } => format!("assert {}, {:?} -> bb{}", show_operand(t, cond), msg, next),
            Term::Pending => "<pending>".into(),
        };
        s.push_str(&format!("    {}\n", term));
    }
    s.push_str("}\n");
    s
}
