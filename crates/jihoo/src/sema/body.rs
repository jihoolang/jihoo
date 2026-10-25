// Lowering function bodies to MIR, checking types on the way.

use super::{expr_path, ty_err, AdtKind, CVal, Env, Owner, Sema, Sym, R};
use crate::ast::{self, ExprKind as E, Mode, RetMode, StmtKind};
use crate::diag::{Diag, Span};
use crate::lex::Op;
use crate::mir::*;
use crate::types::{self, Sig, TyId, TyKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VarKind {
    /// The local holds the value.
    Owned,
    /// The local holds a borrow; the variable is what it points to.
    Borrow,
    /// A closure's captured variable: field `i` of its environment.
    Capture(u32),
}

#[derive(Clone, Copy, Debug)]
pub struct Var {
    pub local: Local,
    pub kind: VarKind,
}

pub struct Scope {
    vars: Vec<(String, Var)>,
    /// Locals to drop and end, in the order they were made.
    locals: Vec<Local>,
    /// A statement's temporaries (not a block).
    temp: bool,
}

struct LoopCtx {
    brk: BlockId,
    cont: BlockId,
    depth: usize,
}

pub struct Fb {
    pub id: FnId,
    pub body: Body,
    pub cur: BlockId,
    scopes: Vec<Scope>,
    loops: Vec<LoopCtx>,
    pub env: Env,
    pub ret_mode: RetMode,
    pub unsafe_depth: u32,
    /// The environment parameter of a closure body.
    pub env_local: Option<Local>,
    /// The next block's value stays a place (the body of a function that
    /// returns `ref` or `inout`).
    pub keep_place: bool,
    /// The place being lowered will be changed: indexing and `deref` take
    /// their mutable forms.
    pub want_mut: bool,
}

/// The result of lowering an expression: a place to read or borrow, or an
/// operand already computed.
#[derive(Clone, Debug)]
pub enum VK {
    Place(Place),
    Op(Operand),
}

#[derive(Clone, Debug)]
pub struct Val {
    pub vk: VK,
    pub ty: TyId,
    /// A temporary holding a new value: it may be moved out of freely.
    pub temp: bool,
}

impl Val {
    pub fn op(o: Operand, ty: TyId) -> Val {
        Val { vk: VK::Op(o), ty, temp: false }
    }
    pub fn place(p: Place, ty: TyId) -> Val {
        Val { vk: VK::Place(p), ty, temp: false }
    }
    pub fn unit() -> Val {
        Val::op(Operand::Const(Const::Zst(types::UNIT)), types::UNIT)
    }
    pub fn never() -> Val {
        Val::op(Operand::Const(Const::Zst(types::NEVER)), types::NEVER)
    }
}

impl Fb {
    pub fn new(id: FnId, env: Env, ret: TyId, ret_mode: RetMode, span: Span) -> Fb {
        let mut fb = Fb {
            id,
            body: Body { locals: Vec::new(), blocks: Vec::new(), arg_count: 0 },
            cur: 0,
            scopes: Vec::new(),
            loops: Vec::new(),
            env,
            ret_mode,
            unsafe_depth: 0,
            env_local: None,
            keep_place: false,
            want_mut: false,
        };
        fb.new_local(ret, None, true, LocalKind::Ret, span);
        fb.cur = fb.new_block();
        fb.scopes.push(Scope { vars: Vec::new(), locals: Vec::new(), temp: false });
        fb
    }

    pub fn new_local(&mut self, ty: TyId, name: Option<String>, mutable: bool, kind: LocalKind, span: Span) -> Local {
        self.body.locals.push(LocalDecl { ty, name, span, mutable, kind });
        (self.body.locals.len() - 1) as Local
    }

    pub fn new_block(&mut self) -> BlockId {
        self.body.blocks.push(Block { stmts: Vec::new(), term: Term::Pending });
        (self.body.blocks.len() - 1) as BlockId
    }

    pub fn push(&mut self, s: Stmt) {
        let c = self.cur as usize;
        self.body.blocks[c].stmts.push(s);
    }

    pub fn assign(&mut self, p: Place, r: Rvalue, span: Span) {
        self.push(Stmt::Assign(p, r, span));
    }

    /// Ends the current block; code after it goes in a new (unreachable
    /// until something jumps there) block.
    pub fn term(&mut self, t: Term) {
        let c = self.cur as usize;
        if matches!(self.body.blocks[c].term, Term::Pending) {
            self.body.blocks[c].term = t;
        }
        self.cur = self.new_block();
    }

    pub fn goto(&mut self, b: BlockId) {
        self.term(Term::Goto(b));
        self.cur = b;
    }

    pub fn switch_to(&mut self, b: BlockId) {
        self.cur = b;
    }

    pub fn ty_of(&self, l: Local) -> TyId {
        self.body.locals[l as usize].ty
    }

    /// A temporary that lives until the end of the current statement.
    pub fn temp(&mut self, ty: TyId, span: Span) -> Local {
        let l = self.new_local(ty, None, true, LocalKind::Temp, span);
        self.push(Stmt::StorageLive(l));
        self.scopes.last_mut().unwrap().locals.push(l);
        l
    }

    /// A temporary that lives until the end of the enclosing block.
    pub fn block_temp(&mut self, ty: TyId, span: Span) -> Local {
        let l = self.new_local(ty, None, true, LocalKind::Temp, span);
        self.push(Stmt::StorageLive(l));
        let i = self.scopes.iter().rposition(|s| !s.temp).unwrap();
        self.scopes[i].locals.push(l);
        l
    }

    pub fn declare(&mut self, name: &str, ty: TyId, mutable: bool, kind: VarKind, span: Span) -> Local {
        let k = if matches!(kind, VarKind::Borrow) { false } else { mutable };
        let l = self.new_local(ty, Some(name.to_string()), k, LocalKind::Var, span);
        self.push(Stmt::StorageLive(l));
        let i = self.scopes.iter().rposition(|s| !s.temp).unwrap();
        self.scopes[i].locals.push(l);
        self.scopes[i].vars.push((name.to_string(), Var { local: l, kind }));
        l
    }

    pub fn bind_var(&mut self, name: &str, v: Var) {
        let i = self.scopes.iter().rposition(|s| !s.temp).unwrap();
        self.scopes[i].vars.push((name.to_string(), v));
    }

    pub fn lookup(&self, name: &str) -> Option<Var> {
        for s in self.scopes.iter().rev() {
            for (n, v) in s.vars.iter().rev() {
                if n == name {
                    return Some(*v);
                }
            }
        }
        None
    }

    pub fn push_scope(&mut self, temp: bool) {
        self.scopes.push(Scope { vars: Vec::new(), locals: Vec::new(), temp });
    }

    pub fn depth(&self) -> usize {
        self.scopes.len()
    }

    pub fn own_param(&mut self, l: Local) {
        self.scopes[0].locals.push(l);
    }

    /// Registers a local made earlier as a temporary of the current scope.
    pub fn add_temp_local(&mut self, l: Local) {
        let c = self.cur as usize;
        self.body.blocks[c].stmts.push(Stmt::StorageLive(l));
        self.scopes.last_mut().unwrap().locals.push(l);
    }
}

impl<'a> Sema<'a> {
    /// The place a variable stands for.
    pub fn var_place(&self, fb: &Fb, v: Var) -> Place {
        match v.kind {
            VarKind::Owned => Place::local(v.local),
            VarKind::Borrow => Place::deref(v.local),
            VarKind::Capture(i) => Place { local: fb.env_local.unwrap(), proj: vec![Proj::Deref, Proj::Field(i), Proj::Deref] },
        }
    }

    /// The type of a place.
    pub fn place_ty(&self, fb: &Fb, p: &Place) -> TyId {
        let mut t = fb.ty_of(p.local);
        let mut variant: Option<u32> = None;
        for pr in &p.proj {
            t = match pr {
                Proj::Deref => self.types.pointee(t).expect("deref of a non-pointer"),
                Proj::Variant(v) => {
                    variant = Some(*v);
                    continue;
                }
                Proj::Field(i) => {
                    if let Some(v) = variant.take() {
                        self.types.variants(t).unwrap()[v as usize].fields[*i as usize]
                    } else {
                        match self.types.kind(t) {
                            TyKind::Slice(e) => {
                                if *i == 0 {
                                    let e = *e;
                                    return self.types_ptr_lookup(e);
                                }
                                types::I64
                            }
                            TyKind::Str => {
                                if *i == 0 {
                                    return self.types_ptr_lookup(types::U8);
                                }
                                types::I64
                            }
                            _ => self.types.field_tys(t)[*i as usize],
                        }
                    }
                }
                Proj::Index(_) => match self.types.kind(t) {
                    TyKind::Array(e, _) => *e,
                    _ => panic!("index of a non-array"),
                },
            };
        }
        t
    }

    fn types_ptr_lookup(&self, e: TyId) -> TyId {
        // Pointer types of views' elements are interned when the view type
        // is made (see `view_ty`).
        self.types.kinds.iter().position(|k| *k == TyKind::Ptr(e)).map(|i| i as TyId).expect("pointer type interned")
    }

    pub fn view_ty(&mut self, k: TyKind) -> TyId {
        match &k {
            TyKind::Slice(e) => {
                self.types.ptr(*e);
            }
            TyKind::Str => {
                self.types.ptr(types::U8);
            }
            _ => {}
        }
        self.types.intern(k)
    }

    pub fn place_mutable(&self, fb: &Fb, p: &Place) -> bool {
        let mut m = fb.body.locals[p.local as usize].mutable;
        let mut t = fb.ty_of(p.local);
        let mut variant: Option<u32> = None;
        for pr in &p.proj {
            match pr {
                Proj::Deref => {
                    m = matches!(self.types.kind(t), TyKind::RefMut(_) | TyKind::Ptr(_));
                    t = self.types.pointee(t).unwrap();
                }
                Proj::Variant(v) => variant = Some(*v),
                Proj::Field(i) => {
                    t = if let Some(v) = variant.take() {
                        self.types.variants(t).unwrap()[v as usize].fields[*i as usize]
                    } else {
                        match self.types.kind(t) {
                            TyKind::Slice(_) | TyKind::Str => return false,
                            _ => self.types.field_tys(t)[*i as usize],
                        }
                    }
                }
                Proj::Index(_) => {
                    if let TyKind::Array(e, _) = self.types.kind(t) {
                        t = *e;
                    }
                }
            }
        }
        m
    }

    /// Whether a value can be moved out of the place: an owned local or its
    /// fields, not through a borrow or an index.
    pub fn place_movable(&self, fb: &Fb, p: &Place) -> Result<(), &'static str> {
        if p.proj.iter().any(|x| matches!(x, Proj::Deref)) {
            return Err("it is borrowed");
        }
        if p.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
            return Err("it is an element of an array");
        }
        if !p.proj.is_empty() {
            return Err("it is part of another value");
        }
        if fb.body.locals[p.local as usize].kind == LocalKind::Arg && self.types.is_ref(fb.ty_of(p.local)) {
            return Err("it is borrowed");
        }
        Ok(())
    }

    // ---- scopes ----

    fn emit_scope_exit(&mut self, fb: &mut Fb, idx: usize) {
        let locals = fb.scopes[idx].locals.clone();
        for &l in locals.iter().rev() {
            let t = fb.ty_of(l);
            if self.types.needs_drop(t) {
                let sp = fb.body.locals[l as usize].span;
                fb.push(Stmt::Drop(Place::local(l), sp));
            }
            fb.push(Stmt::StorageDead(l));
        }
    }

    pub fn pop_scope(&mut self, fb: &mut Fb) {
        let i = fb.scopes.len() - 1;
        self.emit_scope_exit(fb, i);
        fb.scopes.pop();
    }

    /// Drops everything in scopes deeper than `depth` (for `break`,
    /// `return`), without leaving them.
    fn exit_to(&mut self, fb: &mut Fb, depth: usize) {
        for i in (depth..fb.scopes.len()).rev() {
            self.emit_scope_exit(fb, i);
        }
    }

    // ---- functions ----

    pub fn lower_fn(&mut self, id: FnId, decl: u32, env: Env) -> R<()> {
        let info = &self.fns[decl as usize];
        let d = info.decl;
        let f = &self.out[id as usize];
        let sig = f.sig.clone();
        let pass = f.pass.clone();
        let mut fb = Fb::new(id, env.clone(), sig.ret, d.ret_mode, d.name_span);
        if d.is_unsafe {
            fb.unsafe_depth = 1;
        }
        let mut pi = 0;
        let mut lambdas: Vec<(String, Local, FnId)> = Vec::new();
        for p in &d.params {
            if p.mode == Mode::Comptime {
                if let Some(CVal::Lambda(lf, _)) = env.get(&p.name) {
                    let lf = *lf;
                    let l = fb.new_local(sig.params[pi], Some(p.name.clone()), false, LocalKind::Arg, p.span);
                    lambdas.push((p.name.clone(), l, lf));
                    pi += 1;
                }
                continue;
            }
            let t = sig.params[pi];
            let kind = if pass[pi] == ParamPass::Borrow { VarKind::Borrow } else { VarKind::Owned };
            let mutable = p.mode == Mode::Sink;
            let l = fb.new_local(t, Some(p.name.clone()), mutable, LocalKind::Arg, p.span);
            fb.bind_var(&p.name, Var { local: l, kind });
            // An owned parameter is dropped when the function ends.
            if kind == VarKind::Owned {
                fb.own_param(l);
            }
            pi += 1;
        }
        fb.body.arg_count = pi;
        for (n, l, lf) in lambdas {
            self.comptime_closures.push((id, n, l, lf));
        }
        let body = d.body.as_ref().unwrap();
        let ret_val_ty = match d.ret_mode {
            RetMode::Value => sig.ret,
            _ => self.types.pointee(sig.ret).unwrap(),
        };
        self.lower_body(&mut fb, body, ret_val_ty)?;
        self.comptime_closures.retain(|c| c.0 != id);
        self.out[id as usize].body = Some(fb.body);
        Ok(())
    }

    /// The function's block, its value going to the return place.
    fn lower_body(&mut self, fb: &mut Fb, body: &ast::Block, ret_ty: TyId) -> R<()> {
        fb.push_scope(true);
        fb.keep_place = fb.ret_mode != RetMode::Value;
        let v = self.block(fb, body, Some(ret_ty), true)?;
        if v.ty != types::NEVER {
            self.write_return(fb, v, ret_ty, body.tail.as_ref().map(|t| t.span).unwrap_or(body.span))?;
        }
        self.exit_to(fb, 0);
        fb.term(Term::Return);
        Ok(())
    }

    fn write_return(&mut self, fb: &mut Fb, v: Val, ret_ty: TyId, span: Span) -> R<()> {
        match fb.ret_mode {
            RetMode::Value => {
                let v = self.coerce(fb, v, ret_ty, span)?;
                let o = self.operand(fb, v, span)?;
                fb.assign(Place::local(RET), Rvalue::Use(o), span);
            }
            RetMode::Ref | RetMode::Inout => {
                if v.ty != ret_ty {
                    return ty_err(span, &format!("expected `{}`, found `{}`", self.types.show(ret_ty), self.types.show(v.ty)));
                }
                let VK::Place(p) = v.vk else {
                    return ty_err(span, "a function returning `ref` or `inout` returns a place, not a new value");
                };
                if v.temp {
                    return ty_err(span, "this returns a borrow of a temporary value");
                }
                if fb.ret_mode == RetMode::Inout {
                    if !self.place_mutable(fb, &p) {
                        return ty_err(span, "this place cannot be changed, so it cannot be returned as `inout`");
                    }
                    fb.assign(Place::local(RET), Rvalue::RefMut(p), span);
                } else {
                    fb.assign(Place::local(RET), Rvalue::Ref(p), span);
                }
            }
        }
        Ok(())
    }

    // ---- blocks and statements ----

    /// A block; `want` says whether its value is used.
    pub fn block(&mut self, fb: &mut Fb, b: &ast::Block, exp: Option<TyId>, want: bool) -> R<Val> {
        let keep_place = std::mem::replace(&mut fb.keep_place, false);
        // A block expected to give `()` throws its last value away.
        let want = want && exp != Some(types::UNIT);
        let exp = if want { exp } else { None };
        fb.push_scope(false);
        let mut diverged = false;
        for s in &b.stmts {
            fb.push_scope(true);
            let r = self.stmt(fb, s)?;
            self.pop_scope(fb);
            if r {
                diverged = true;
            }
        }
        let result = match &b.tail {
            Some(t) => {
                fb.push_scope(true);
                if keep_place {
                    // `unsafe { *p }` as a function's `ref` result.
                    if let E::Unsafe(_) | E::Block(_) = &t.kind {
                        fb.keep_place = true;
                    }
                }
                let v = self.expr(fb, t, if want { exp } else { None })?;
                let out = if v.ty == types::NEVER {
                    Val::never()
                } else if keep_place && matches!(v.vk, VK::Place(_)) && !v.temp {
                    // The place may start at a pointer in a temporary of the
                    // block: keep that pointer in one that outlives it.
                    let VK::Place(p) = v.vk.clone() else { unreachable!() };
                    let root = &fb.body.locals[p.local as usize];
                    if root.kind == LocalKind::Temp && p.proj.first() == Some(&Proj::Deref) {
                        let rt = root.ty;
                        let n = fb.scopes.len();
                        let tmp = fb.new_local(rt, None, true, LocalKind::Temp, t.span);
                        fb.push(Stmt::StorageLive(tmp));
                        fb.scopes[n - 3].locals.push(tmp);
                        fb.assign(Place::local(tmp), Rvalue::Use(Operand::Copy(Place::local(p.local))), t.span);
                        Val { vk: VK::Place(Place { local: tmp, proj: p.proj.clone() }), ty: v.ty, temp: false }
                    } else {
                        v
                    }
                } else if want && v.ty != types::UNIT {
                    let v = match exp {
                        Some(e) => self.coerce(fb, v, e, t.span)?,
                        None => v,
                    };
                    // The value outlives the block's scopes: move it to the
                    // statement around the block.
                    let o = self.operand(fb, v.clone(), t.span)?;
                    let n = fb.scopes.len();
                    let tmp = fb.new_local(v.ty, None, true, LocalKind::Temp, t.span);
                    fb.push(Stmt::StorageLive(tmp));
                    fb.scopes[n - 3].locals.push(tmp);
                    fb.assign(Place::local(tmp), Rvalue::Use(o), t.span);
                    Val { vk: VK::Place(Place::local(tmp)), ty: v.ty, temp: true }
                } else {
                    self.discard(fb, v, t.span)?;
                    Val::unit()
                };
                self.pop_scope(fb);
                out
            }
            None if diverged => Val::never(),
            None => Val::unit(),
        };
        self.pop_scope(fb);
        Ok(result)
    }

    /// Evaluates and throws away a value (an expression statement).
    fn discard(&mut self, fb: &mut Fb, v: Val, span: Span) -> R<()> {
        if let VK::Op(o) = v.vk {
            if let Operand::Move(_) = o {
                let t = fb.temp(v.ty, span);
                fb.assign(Place::local(t), Rvalue::Use(o), span);
            }
        }
        Ok(())
    }

    /// One statement; returns whether it never finishes (`return`, ...).
    fn stmt(&mut self, fb: &mut Fb, s: &ast::Stmt) -> R<bool> {
        match &s.kind {
            StmtKind::Expr(e) => {
                let v = self.expr(fb, e, None)?;
                let never = v.ty == types::NEVER;
                self.discard(fb, v, e.span)?;
                Ok(never)
            }
            StmtKind::Let { kind, pat, ty, value } => {
                self.let_stmt(fb, *kind, pat, ty.as_ref(), value, s.span)?;
                Ok(false)
            }
            StmtKind::Assign(place, value) => {
                // The value first, then the place: `c[i] = c[i] + 1` borrows
                // `c` mutably only once the value is computed.
                let guess = self.peek_type(fb, place);
                let v = self.expr(fb, value, guess)?;
                let v = self.value_operand_val(fb, v, value.span)?;
                let pv = self.expr_mut(fb, place)?;
                let VK::Place(p) = pv.vk.clone() else { return ty_err(place.span, "cannot assign to this") };
                if pv.temp {
                    return ty_err(place.span, "cannot assign to a temporary value");
                }
                let v = self.coerce(fb, v, pv.ty, value.span)?;
                if !self.place_mutable(fb, &p) {
                    return ty_err(place.span, &self.not_mutable_msg(fb, &p));
                }
                let o = self.operand(fb, v, value.span)?;
                if self.types.needs_drop(pv.ty) {
                    fb.push(Stmt::Drop(p.clone(), s.span));
                }
                fb.assign(p, Rvalue::Use(o), s.span);
                Ok(false)
            }
            StmtKind::OpAssign(op, place, value) if !self.peek_is_adt(fb, place) => {
                // Numbers: the value first, then the place.
                let guess = self.peek_type(fb, place);
                let v = self.expr(fb, value, guess)?;
                let v = self.value_operand_val(fb, v, value.span)?;
                let pv = self.expr_mut(fb, place)?;
                let VK::Place(p) = pv.vk.clone() else { return ty_err(place.span, "cannot assign to this") };
                if self.types.adt_of(pv.ty).is_some() {
                    return ty_err(place.span, "internal: op-assign on a struct took the number path");
                }
                if !self.place_mutable(fb, &p) {
                    return ty_err(place.span, &self.not_mutable_msg(fb, &p));
                }
                let lhs = Val::op(Operand::Copy(p.clone()), pv.ty);
                let r = self.binary_vals(fb, *op, lhs, v, s.span)?;
                let o = self.operand(fb, r, s.span)?;
                fb.assign(p, Rvalue::Use(o), s.span);
                Ok(false)
            }
            StmtKind::OpAssign(op, place, value) => {
                let pv = self.expr_mut(fb, place)?;
                let VK::Place(p) = pv.vk.clone() else { return ty_err(place.span, "cannot assign to this") };
                if self.types.adt_of(pv.ty).is_some() {
                    // `s += x` calls `add_assign(inout self, x)`.
                    let name = match op {
                        Op::Add => "add_assign",
                        Op::Sub => "sub_assign",
                        _ => return ty_err(s.span, &format!("`{}=` is not defined for `{}`", op.text(), self.types.show(pv.ty))),
                    };
                    let recv = Val::place(p, pv.ty);
                    self.method_call(fb, recv, name, std::slice::from_ref(value), s.span, None, true)?;
                    return Ok(false);
                }
                if !self.place_mutable(fb, &p) {
                    return ty_err(place.span, &self.not_mutable_msg(fb, &p));
                }
                let lhs = Operand::Copy(p.clone());
                let r = self.binary_on(fb, *op, Val::op(lhs, pv.ty), value, s.span)?;
                let o = self.operand(fb, r, s.span)?;
                fb.assign(p, Rvalue::Use(o), s.span);
                Ok(false)
            }
        }
    }

    pub fn not_mutable_msg(&self, fb: &Fb, p: &Place) -> String {
        let l = &fb.body.locals[p.local as usize];
        match (&l.name, p.proj.first()) {
            (Some(n), None) => format!("`{}` cannot be changed; declare it with `var`", n),
            (Some(n), Some(Proj::Deref)) if l.kind == LocalKind::Arg => {
                format!("`{}` is borrowed read-only; make the parameter `inout` to change it", n)
            }
            (Some(n), _) if l.mutable => format!("this part of `{}` cannot be changed", n),
            (Some(n), _) => format!("`{}` cannot be changed; declare it with `var`", n),
            _ => "this place cannot be changed".to_string(),
        }
    }

    fn let_stmt(&mut self, fb: &mut Fb, kind: ast::LetKind, pat: &ast::Pat, ty: Option<&ast::Ty>, value: &ast::Expr, span: Span) -> R<()> {
        let env = fb.env.clone();
        let exp = match ty {
            Some(t) => Some(self.resolve_ty(t, &env)?),
            None => None,
        };
        if kind == ast::LetKind::Inout {
            let ast::PatKind::Name(name, _) = &pat.kind else { return ty_err(pat.span, "`inout` binds one name") };
            let (p, t) = self.mut_place(fb, value)?;
            if let Some(e) = exp {
                if e != t {
                    return ty_err(value.span, &format!("expected `{}`, found `{}`", self.types.show(e), self.types.show(t)));
                }
            }
            let rt = self.types.refmut(t);
            let l = fb.declare(name, rt, false, VarKind::Borrow, pat.span);
            fb.assign(Place::local(l), Rvalue::RefMut(p), span);
            return Ok(());
        }
        let v = self.expr(fb, value, exp)?;
        let v = match exp {
            Some(e) => self.coerce(fb, v, e, value.span)?,
            None => v,
        };
        if v.ty == types::NEVER {
            return Ok(());
        }
        match &pat.kind {
            ast::PatKind::Name(name, var) if !self.names_variant(fb, name, v.ty) => {
                let mutable = kind == ast::LetKind::Var || *var;
                self.bind_name(fb, name, v, mutable, pat.span)?;
                Ok(())
            }
            _ => {
                let mode = if kind == ast::LetKind::Var { super::pat::BindMode::Owned } else { super::pat::BindMode::Auto };
                self.destructure(fb, pat, v, mode, value.span)
            }
        }
    }

    /// `let x = v`: a borrow of a place that is not plain, else an owned
    /// value.
    pub fn bind_name(&mut self, fb: &mut Fb, name: &str, v: Val, mutable: bool, span: Span) -> R<Local> {
        if self.types.kind(v.ty) == &TyKind::Type {
            return ty_err(span, "types exist only while compiling; use `comptime` or a constant");
        }
        if self.types.is_ref(v.ty) {
            let t = v.ty;
            let o = self.operand(fb, v, span)?;
            let l = fb.declare(name, t, false, VarKind::Borrow, span);
            fb.assign(Place::local(l), Rvalue::Use(o), span);
            return Ok(l);
        }
        if let VK::Place(p) = &v.vk {
            if !mutable && !v.temp && !self.types.is_plain(v.ty) {
                let rt = self.types.refty(v.ty);
                let l = fb.declare(name, rt, false, VarKind::Borrow, span);
                fb.assign(Place::local(l), Rvalue::Ref(p.clone()), span);
                return Ok(l);
            }
        }
        let t = v.ty;
        let o = self.operand(fb, v, span)?;
        let l = fb.declare(name, t, mutable, VarKind::Owned, span);
        fb.assign(Place::local(l), Rvalue::Use(o), span);
        Ok(l)
    }

    pub fn names_variant(&self, fb: &Fb, name: &str, t: TyId) -> bool {
        if fb.lookup(name).is_some() {
            return false;
        }
        self.types.variants(t).map(|vs| vs.iter().any(|v| v.name == name && v.fields.is_empty())).unwrap_or(false)
    }

    // ---- values ----

    /// The operand for a value used up: a copy of a plain place, or a move.
    pub fn operand(&mut self, fb: &mut Fb, v: Val, span: Span) -> R<Operand> {
        // A part of a temporary (`pair().1`): it moves out now, and the
        // temporary's other parts are dropped, so that it is never dropped
        // whole with a part missing.
        if let VK::Place(p) = &v.vk {
            let whole = fb.ty_of(p.local);
            if v.temp
                && !p.proj.is_empty()
                && p.proj.iter().all(|x| matches!(x, Proj::Field(_) | Proj::Variant(_)))
                && fb.body.locals[p.local as usize].kind == LocalKind::Temp
                && !self.types.is_plain(v.ty)
                && self.types.needs_drop(whole)
            {
                let p = p.clone();
                let t = fb.temp(v.ty, span);
                fb.assign(Place::local(t), Rvalue::Use(Operand::Move(p.clone())), span);
                self.drop_others(fb, Place::local(p.local), whole, &p.proj, span)?;
                fb.push(Stmt::Forget(p.local));
                return Ok(Operand::Move(Place::local(t)));
            }
        }
        self.operand_part(fb, v, span)
    }

    /// The other parts of a temporary than the one at `path` (below `base`,
    /// of type `ty`), dropped.
    fn drop_others(&mut self, fb: &mut Fb, base: Place, ty: TyId, path: &[Proj], span: Span) -> R<()> {
        if !path.is_empty() && self.types.adt_of(ty).map(|a| a.has_drop).unwrap_or(false) {
            return ty_err(span, &format!("cannot move a part out of a `{}`: it has a `Drop` impl", self.types.show(ty)));
        }
        let (parts, here, rest) = match path {
            [Proj::Variant(v), Proj::Field(i), rest @ ..] => {
                let fts = self.types.variants(ty).unwrap()[*v as usize].fields.clone();
                let ps: Vec<Place> = (0..fts.len()).map(|j| base.with(Proj::Variant(*v)).with(Proj::Field(j as u32))).collect();
                (ps.into_iter().zip(fts).collect::<Vec<_>>(), *i as usize, rest)
            }
            [Proj::Field(i), rest @ ..] => {
                let fts = self.types.field_tys(ty);
                let ps: Vec<Place> = (0..fts.len()).map(|j| base.with(Proj::Field(j as u32))).collect();
                (ps.into_iter().zip(fts).collect::<Vec<_>>(), *i as usize, rest)
            }
            _ => return Ok(()),
        };
        for (j, (fp, ft)) in parts.into_iter().enumerate() {
            if j == here {
                self.drop_others(fb, fp, ft, rest, span)?;
            } else if self.types.needs_drop(ft) {
                fb.push(Stmt::Drop(fp, span));
            }
        }
        Ok(())
    }

    /// An operand for a value; a part of a temporary moves out alone (for
    /// patterns, which drop the other parts themselves).
    pub fn operand_part(&mut self, fb: &mut Fb, v: Val, span: Span) -> R<Operand> {
        match v.vk {
            VK::Op(o) => Ok(o),
            VK::Place(p) => {
                if self.types.is_plain(v.ty) {
                    return Ok(Operand::Copy(p));
                }
                if v.temp {
                    return Ok(Operand::Move(p));
                }
                if let Err(why) = self.place_movable(fb, &p) {
                    let what = self.describe_place(fb, &p);
                    return ty_err(
                        span,
                        &format!("cannot move {} out of its place: {}; use `.clone()` to copy it, or `std.mem.take`/`replace`", what, why),
                    );
                }
                Ok(Operand::Move(p))
            }
        }
    }

    pub fn describe_place(&self, fb: &Fb, p: &Place) -> String {
        match &fb.body.locals[p.local as usize].name {
            Some(n) if p.proj.is_empty() || (p.proj.len() == 1 && p.proj[0] == Proj::Deref) => format!("`{}`", n),
            Some(n) => format!("a part of `{}`", n),
            None => "this value".to_string(),
        }
    }

    /// A place holding the value: the place itself, or a temporary.
    pub fn as_place(&mut self, fb: &mut Fb, v: Val, span: Span) -> (Place, bool) {
        match v.vk {
            VK::Place(p) => (p, v.temp),
            VK::Op(o) => {
                let t = fb.temp(v.ty, span);
                fb.assign(Place::local(t), Rvalue::Use(o), span);
                (Place::local(t), true)
            }
        }
    }

    /// Puts an rvalue in a fresh temporary.
    pub fn rvalue(&mut self, fb: &mut Fb, r: Rvalue, ty: TyId, span: Span) -> Val {
        let t = fb.temp(ty, span);
        fb.assign(Place::local(t), r, span);
        Val { vk: VK::Place(Place::local(t)), ty, temp: true }
    }

    /// A place to change, from `&place`: an `inout` argument, or the value
    /// of `inout x = &place`. The `&` is required, so that the reader sees
    /// what may change.
    pub fn mut_place(&mut self, fb: &mut Fb, e: &ast::Expr) -> R<(Place, TyId)> {
        let E::Unary(ast::UnOp::Addr, inner) = &e.kind else {
            return ty_err(e.span, "this is changed through an `inout` parameter, so write `&` before it");
        };
        let v = self.expr_mut(fb, inner)?;
        let VK::Place(p) = v.vk else { return ty_err(e.span, "expected a place (a variable, a field, an element)") };
        if !self.place_mutable(fb, &p) {
            return ty_err(e.span, &self.not_mutable_msg(fb, &p));
        }
        Ok((p, v.ty))
    }

    /// Converts a value to the expected type, where the language allows it.
    pub fn coerce(&mut self, fb: &mut Fb, v: Val, to: TyId, span: Span) -> R<Val> {
        if v.ty == to || v.ty == types::NEVER {
            return Ok(Val { ty: if v.ty == types::NEVER { types::NEVER } else { to }, ..v });
        }
        let from = v.ty;
        // An integer literal typed before its type was known.
        if let VK::Op(Operand::Const(Const::Int(x, _))) = &v.vk {
            if self.types.is_int(to) && self.types.is_int(from) && self.int_fits(*x, to) {
                return Ok(Val::op(Operand::Const(Const::Int(*x, to)), to));
            }
            if self.types.is_float(to) && self.types.is_int(from) && (*x as f64) as i128 == *x {
                return Ok(Val::op(Operand::Const(Const::Float(*x as f64, to)), to));
            }
        }
        // A borrow held as a value (`ref T`) where a `T` is expected: what it
        // points to, lent on (moving out of it is still an error).
        if let TyKind::Ref(inner) | TyKind::RefMut(inner) = self.types.kind(from).clone() {
            if inner == to {
                return self.auto_deref(fb, v, span);
            }
        }
        // A place where a borrow of it is expected.
        if let TyKind::Ref(inner) | TyKind::RefMut(inner) = self.types.kind(to).clone() {
            if inner == from {
                let m = matches!(self.types.kind(to), TyKind::RefMut(_));
                let (p, temp) = self.as_place(fb, v, span);
                if temp {
                    return ty_err(span, "this would borrow a temporary value, which does not live long enough");
                }
                if m && !self.place_mutable(fb, &p) {
                    return ty_err(span, &self.not_mutable_msg(fb, &p));
                }
                return Ok(self.rvalue(fb, if m { Rvalue::RefMut(p) } else { Rvalue::Ref(p) }, to, span));
            }
        }
        // A string literal where a C string is expected: its bytes end
        // with a zero.
        if from == types::STR && Some(to) == self.types_ptr_u8_opt() {
            if let VK::Op(Operand::Const(Const::Str(_))) = &v.vk {
                let (p, _) = self.as_place(fb, v, span);
                return Ok(Val::op(Operand::Copy(p.with(Proj::Field(0))), to));
            }
        }
        // A string literal where a `String` is expected: no allocation.
        if Some(to) == self.string_ty() && from == types::STR {
            if let VK::Op(Operand::Const(Const::Str(_))) = &v.vk {
                return self.call_static(fb, to, "from_static", vec![v], span);
            }
        }
        // `[T; N]` place to `[T]`.
        if let (TyKind::Array(e, n), TyKind::Slice(e2)) = (self.types.kind(from).clone(), self.types.kind(to).clone()) {
            if e == e2 {
                let (p, _) = self.as_place(fb, v, span);
                let pt = self.types.ptr(e);
                let addr = if n == 0 {
                    Operand::Const(Const::Null(pt))
                } else {
                    let fp = self.types.ptr(from);
                    let a = self.rvalue(fb, Rvalue::Addr(p), fp, span);
                    let ap = self.place_of_val(a);
                    let c = self.rvalue(fb, Rvalue::Cast(Operand::Copy(ap), pt, CastKind::Ptr), pt, span);
                    Operand::Copy(self.place_of_val(c))
                };
                let vt = self.view_ty(TyKind::Slice(e));
                return Ok(self.rvalue(fb, Rvalue::Aggregate(Agg::View(vt), vec![addr, Operand::Const(Const::Int(n as i128, types::I64))]), vt, span));
            }
        }
        // A library type to its view: `String` to `str`, `Vec(T)` to `[T]`.
        if matches!(self.types.kind(to), TyKind::Str | TyKind::Slice(_)) && self.types.adt_of(from).is_some() {
            let name = if to == types::STR { "as_str" } else { "as_slice" };
            if self.find_method(from, name)?.is_some() {
                let r = self.method_call_val(fb, v.clone(), name, vec![], span, Some(to))?;
                if r.ty == to {
                    return Ok(r);
                }
            }
        }
        // Through `deref` (a `Box(T)` where a `T` is borrowed).
        if self.types.adt_of(from).is_some() && self.find_method(from, "deref")?.is_some() {
            let d = self.method_call_val(fb, v.clone(), "deref", vec![], span, None)?;
            if d.ty == to {
                return Ok(d);
            }
            if self.types.adt_of(d.ty).is_some() {
                if let Ok(r) = self.coerce(fb, d, to, span) {
                    return Ok(r);
                }
            }
        }
        // `null` and integer constants to pointers are done by `expr`.
        // A named function where a closure is expected.
        if let (VK::Op(Operand::Const(Const::Fn(f))), TyKind::Closure(sig)) = (&v.vk, self.types.kind(to).clone()) {
            if let TyKind::FnPtr(fsig) = self.types.kind(from).clone() {
                if fsig == sig {
                    let w = self.closure_thunk(*f, &sig)?;
                    let null = Operand::Const(Const::Null(self.types.ptr(types::U8)));
                    return Ok(self.rvalue(fb, Rvalue::Aggregate(Agg::Closure(to), vec![Operand::Const(Const::Fn(w)), null]), to, span));
                }
            }
        }
        ty_err(span, &format!("expected `{}`, found `{}`", self.types.show(to), self.types.show(from)))
    }

    fn types_ptr_u8(&mut self) -> TyId {
        self.types.ptr(types::U8)
    }

    fn types_ptr_u8_opt(&mut self) -> Option<TyId> {
        Some(self.types.ptr(types::U8))
    }

    pub fn place_of_val(&self, v: Val) -> Place {
        match v.vk {
            VK::Place(p) => p,
            VK::Op(_) => panic!("place_of_val on an operand"),
        }
    }

    pub fn string_ty(&mut self) -> Option<TyId> {
        let d = self.lang.string?;
        self.adt_instance(d, Vec::new(), Span::default()).ok()
    }

    /// A function taking an ignored environment first and calling `f`, so
    /// a named function can stand where a closure is expected.
    fn closure_thunk(&mut self, f: FnId, sig: &Sig) -> R<FnId> {
        let id = self.out.len() as FnId;
        let envp = self.types.ptr(types::U8);
        let mut params = vec![envp];
        params.extend(sig.params.iter().copied());
        let target = &self.out[f as usize];
        let mut pass = vec![ParamPass::Value];
        pass.extend(target.pass.iter().copied());
        let mut fb = Fb::new(id, Env::default(), sig.ret, RetMode::Value, target.span);
        let mut args = Vec::new();
        for (i, &t) in params.iter().enumerate() {
            let l = fb.new_local(t, None, false, LocalKind::Arg, target.span);
            if i > 0 {
                args.push(if self.types.is_plain(t) { Operand::Copy(Place::local(l)) } else { Operand::Move(Place::local(l)) });
            }
        }
        fb.body.arg_count = params.len();
        let next = fb.new_block();
        let sp = target.span;
        fb.term(Term::Call { callee: Callee::Fn(f), args, dest: Place::local(RET), next, span: sp });
        fb.switch_to(next);
        fb.term(Term::Return);
        self.out.push(Function {
            symbol: format!("thunk.{}", id),
            name: format!("thunk for {}", self.out[f as usize].name),
            sig: Sig { params, ret: sig.ret },
            pass,
            body: Some(fb.body),
            linkage: Linkage::Internal,
            variadic: false,
            returns_ref: false,
            span: sp,
        });
        self.inst_info.push(None);
        Ok(id)
    }

    // ---- expressions ----

    /// Lowers a place that will be changed.
    pub fn expr_mut(&mut self, fb: &mut Fb, e: &ast::Expr) -> R<Val> {
        fb.want_mut = true;
        self.expr(fb, e, None)
    }

    pub fn expr(&mut self, fb: &mut Fb, e: &ast::Expr, exp: Option<TyId>) -> R<Val> {
        let span = e.span;
        let wm = std::mem::replace(&mut fb.want_mut, false);
        match &e.kind {
            E::Field(base, name) if wm => {
                if let Some(p) = expr_path(e) {
                    if fb.lookup(&p[0]).is_none() {
                        return self.field_expr(fb, e, base, name, exp);
                    }
                }
                let bv = self.expr_mut(fb, base)?;
                fb.want_mut = true;
                let r = self.field_of(fb, bv, name, span);
                fb.want_mut = false;
                r
            }
            E::TupleField(base, i) if wm => {
                let bv = self.expr_mut(fb, base)?;
                fb.want_mut = true;
                let bv = self.auto_deref(fb, bv, span);
                fb.want_mut = false;
                let bv = bv?;
                let TyKind::Tuple(ts) = self.types.kind(bv.ty).clone() else {
                    return ty_err(span, &format!("`.{}` needs a tuple, found `{}`", i, self.types.show(bv.ty)));
                };
                if *i as usize >= ts.len() {
                    return ty_err(span, &format!("this tuple has {} parts", ts.len()));
                }
                let temp = bv.temp;
                let (p, _) = self.as_place(fb, bv, span);
                Ok(Val { vk: VK::Place(p.with(Proj::Field(*i))), ty: ts[*i as usize], temp })
            }
            E::Index(base, idx) if wm => self.index_expr(fb, base, idx, span, true),
            E::Unary(ast::UnOp::Deref, inner) if wm => {
                let v = self.expr_mut(fb, inner)?;
                match self.types.kind(v.ty).clone() {
                    TyKind::Ptr(_) => self.auto_deref(fb, v, span),
                    TyKind::Adt(_) if self.find_method(v.ty, "deref_mut")?.is_some() => self.method_call_val(fb, v, "deref_mut", vec![], span, None),
                    _ => self.expr(fb, e, exp),
                }
            }
            _ => self.expr_plain(fb, e, exp, span),
        }
    }

    fn expr_plain(&mut self, fb: &mut Fb, e: &ast::Expr, exp: Option<TyId>, span: Span) -> R<Val> {
        match &e.kind {
            E::Int(v) => {
                let t = match exp {
                    Some(t) if self.types.is_int(t) => t,
                    Some(t) if self.types.is_float(t) => {
                        let f = *v as f64;
                        if f as u64 != *v {
                            return ty_err(span, "this integer is not exact as a float");
                        }
                        return Ok(Val::op(Operand::Const(Const::Float(f, t)), t));
                    }
                    _ => types::I64,
                };
                if !self.int_fits(*v as i128, t) {
                    return ty_err(span, &format!("{} does not fit in `{}`", v, self.types.show(t)));
                }
                Ok(Val::op(Operand::Const(Const::Int(*v as i128, t)), t))
            }
            E::Char(c) => {
                let t = exp.filter(|&t| self.types.is_int(t)).unwrap_or(types::U8);
                Ok(Val::op(Operand::Const(Const::Int(*c as i128, t)), t))
            }
            E::Float(f) => {
                let t = exp.filter(|&t| self.types.is_float(t)).unwrap_or(types::F64);
                let v = if t == types::F32 { *f as f32 as f64 } else { *f };
                Ok(Val::op(Operand::Const(Const::Float(v, t)), t))
            }
            E::Bool(b) => Ok(Val::op(Operand::Const(Const::Bool(*b)), types::BOOL)),
            E::Str(s) => {
                self.view_ty(TyKind::Str);
                Ok(Val::op(Operand::Const(Const::Str(s.clone())), types::STR))
            }
            E::Unit => Ok(Val::unit()),
            E::Name(n) => self.name_expr(fb, n, exp, span),
            E::Field(base, name) => self.field_expr(fb, e, base, name, exp),
            E::TupleField(base, i) => {
                let bv = self.expr(fb, base, None)?;
                let bv = self.auto_deref(fb, bv, span)?;
                let TyKind::Tuple(ts) = self.types.kind(bv.ty).clone() else {
                    return ty_err(span, &format!("`.{}` needs a tuple, found `{}`", i, self.types.show(bv.ty)));
                };
                if *i as usize >= ts.len() {
                    return ty_err(span, &format!("this tuple has {} parts", ts.len()));
                }
                let temp = bv.temp;
                let (p, _) = self.as_place(fb, bv, span);
                Ok(Val { vk: VK::Place(p.with(Proj::Field(*i))), ty: ts[*i as usize], temp })
            }
            E::Call(callee, args) => self.call_expr(fb, callee, args, exp, span),
            E::Index(base, idx) => self.index_expr(fb, base, idx, span, false),
            E::Unary(op, inner) => self.unary_expr(fb, *op, inner, exp, span),
            E::Binary(op, a, b) => {
                if matches!(op, Op::LogAnd | Op::LogOr) {
                    return self.logic(fb, *op, a, b, span);
                }
                // A shift has its left side's type, so `let b: u8 = 1 << 3`
                // makes the `1` a `u8`.
                let ea = if op.is_compare() { None } else { exp };
                let mut av = self.expr(fb, a, ea)?;
                // `1 + x`: let the literal take the other side's type (not for
                // a shift, whose sides may differ).
                if matches!(a.kind, E::Int(_) | E::Float(_) | E::Char(_)) && ea.is_none() && !matches!(op, Op::Shl | Op::Shr) &&!matches!(b.kind, E::Int(_) | E::Float(_) | E::Char(_)) {
                    let probe = self.peek_type(fb, b);
                    if let Some(bt) = probe {
                        if self.types.is_int(bt) || self.types.is_float(bt) {
                            av = self.expr(fb, a, Some(bt))?;
                        }
                    }
                }
                self.binary_on(fb, *op, av, b, span)
            }
            E::Cast(inner, t) => {
                let env = fb.env.clone();
                let to = self.resolve_ty(t, &env)?;
                self.cast(fb, inner, to, span)
            }
            E::Try(inner) => self.try_expr(fb, inner, span),
            E::Move(inner) => {
                let v = self.expr(fb, inner, exp)?;
                let VK::Place(p) = v.vk.clone() else { return Ok(v) };
                if !v.temp {
                    if let Err(why) = self.place_movable(fb, &p) {
                        return ty_err(span, &format!("cannot move {}: {}", self.describe_place(fb, &p), why));
                    }
                }
                Ok(Val { vk: VK::Op(Operand::Move(p)), ty: v.ty, temp: false })
            }
            E::StructLit(path, fields) => self.struct_lit(fb, path, fields, exp, span),
            E::Tuple(items) => {
                let exps: Vec<Option<TyId>> = match exp.map(|t| self.types.kind(t).clone()) {
                    Some(TyKind::Tuple(ts)) if ts.len() == items.len() => ts.into_iter().map(Some).collect(),
                    _ => vec![None; items.len()],
                };
                let mut ops = Vec::new();
                let mut tys = Vec::new();
                for (it, ex) in items.iter().zip(exps) {
                    let v = self.expr(fb, it, ex)?;
                    let v = match ex {
                        Some(t) => self.coerce(fb, v, t, it.span)?,
                        None => v,
                    };
                    tys.push(v.ty);
                    ops.push(self.operand(fb, v, it.span)?);
                }
                let t = self.types.tuple(tys);
                Ok(self.rvalue(fb, Rvalue::Aggregate(Agg::Struct(t), ops), t, span))
            }
            E::Array(items) => {
                let ee = match exp.map(|t| self.types.kind(t).clone()) {
                    Some(TyKind::Array(e, _)) | Some(TyKind::Slice(e)) => Some(e),
                    _ => None,
                };
                // `[]` where a slice is expected: an empty view.
                if let (true, Some(TyKind::Slice(e))) = (items.is_empty(), exp.map(|t| self.types.kind(t).clone())) {
                    let vt = self.view_ty(TyKind::Slice(e));
                    let pt = self.types.ptr(e);
                    let ops = vec![Operand::Const(Const::Null(pt)), Operand::Const(Const::Int(0, types::I64))];
                    return Ok(self.rvalue(fb, Rvalue::Aggregate(Agg::View(vt), ops), vt, span));
                }
                if items.is_empty() {
                    let Some(et) = ee else { return ty_err(span, "the type of an empty array must be known: write `let a: [T; 0] = []`") };
                    let t = self.types.intern(TyKind::Array(et, 0));
                    return Ok(Val::op(Operand::Const(Const::Zst(t)), t));
                }
                let mut ops = Vec::new();
                let mut et = ee;
                for it in items {
                    let v = self.expr(fb, it, et)?;
                    let v = match et {
                        Some(t) => self.coerce(fb, v, t, it.span)?,
                        None => v,
                    };
                    et = Some(v.ty);
                    ops.push(self.operand(fb, v, it.span)?);
                }
                let t = self.types.intern(TyKind::Array(et.unwrap(), items.len() as u64));
                Ok(self.rvalue(fb, Rvalue::Aggregate(Agg::Array(t), ops), t, span))
            }
            E::ArrayRepeat(el, n) => {
                let ee = match exp.map(|t| self.types.kind(t).clone()) {
                    Some(TyKind::Array(e, _)) => Some(e),
                    _ => None,
                };
                let env = fb.env.clone();
                let n = self.const_int(n, &env)?;
                if n < 0 {
                    return ty_err(span, "an array's length cannot be negative");
                }
                let v = self.expr(fb, el, ee)?;
                let v = match ee {
                    Some(t) => self.coerce(fb, v, t, el.span)?,
                    None => v,
                };
                if !self.types.is_plain(v.ty) {
                    return ty_err(el.span, "`[x; n]` copies `x`, so it must be a plain value; build the array with a loop");
                }
                let et = v.ty;
                let o = self.operand(fb, v, el.span)?;
                let t = self.types.intern(TyKind::Array(et, n as u64));
                Ok(self.rvalue(fb, Rvalue::Repeat(o, n as u64), t, span))
            }
            E::Block(b) => self.block(fb, b, exp, true),
            E::Unsafe(b) => {
                fb.unsafe_depth += 1;
                let r = self.block(fb, b, exp, true);
                fb.unsafe_depth -= 1;
                r
            }
            E::Comptime(inner) => {
                let env = fb.env.clone();
                let (c, t) = self.const_expr(inner, &env, exp)?;
                Ok(Val::op(Operand::Const(c), t))
            }
            E::If(c, then, els) => self.if_expr(fb, c, then, els.as_deref(), exp, span),
            E::Match(scrut, arms) => self.match_expr(fb, scrut, arms, exp, span),
            E::While(c, body) => {
                let head = fb.new_block();
                let exit = fb.new_block();
                fb.goto(head);
                let cv = self.expr(fb, c, Some(types::BOOL))?;
                let cv = self.coerce(fb, cv, types::BOOL, c.span)?;
                let co = self.operand(fb, cv, c.span)?;
                let bb = fb.new_block();
                fb.term(Term::Switch { discr: co, targets: vec![(0, exit)], otherwise: bb });
                fb.switch_to(bb);
                fb.loops.push(LoopCtx { brk: exit, cont: head, depth: fb.depth() });
                self.block(fb, body, Some(types::UNIT), false)?;
                fb.loops.pop();
                fb.goto(head);
                fb.switch_to(exit);
                Ok(Val::unit())
            }
            E::Loop(body) => {
                let head = fb.new_block();
                let exit = fb.new_block();
                fb.goto(head);
                fb.loops.push(LoopCtx { brk: exit, cont: head, depth: fb.depth() });
                self.block(fb, body, Some(types::UNIT), false)?;
                fb.loops.pop();
                fb.goto(head);
                fb.switch_to(exit);
                // A loop without `break` never ends.
                let reached = self.block_reached(fb, exit);
                Ok(if reached { Val::unit() } else { Val::never() })
            }
            E::For(index, pat, it, body) => self.for_expr(fb, index.as_ref(), pat, it, body, span),
            E::Lambda(params, ret, body) => self.lambda(fb, params, ret.as_ref(), body, exp, span),
            E::Return(v) => {
                let ret_ty = match fb.ret_mode {
                    RetMode::Value => fb.ty_of(RET),
                    _ => self.types.pointee(fb.ty_of(RET)).unwrap(),
                };
                match v {
                    Some(v) => {
                        let val = self.expr(fb, v, Some(ret_ty))?;
                        if val.ty == types::NEVER {
                            return Ok(Val::never());
                        }
                        self.write_return(fb, val, ret_ty, v.span)?;
                    }
                    None => {
                        if ret_ty != types::UNIT {
                            return ty_err(span, &format!("this function returns `{}`", self.types.show(ret_ty)));
                        }
                    }
                }
                self.exit_to(fb, 0);
                fb.term(Term::Return);
                Ok(Val::never())
            }
            E::Break | E::Continue => {
                let Some(l) = fb.loops.last() else { return ty_err(span, "`break` and `continue` belong in a loop") };
                let (target, depth) = (if matches!(e.kind, E::Break) { l.brk } else { l.cont }, l.depth);
                self.exit_to(fb, depth);
                fb.term(Term::Goto(target));
                Ok(Val::never())
            }
            E::Range(..) => ty_err(span, "a range only goes in a `for` loop or a slice (`xs[a..b]`)"),
            E::Type(_) => ty_err(span, "a type is not a value here"),
        }
    }

    fn block_reached(&self, fb: &Fb, b: BlockId) -> bool {
        fb.body.blocks.iter().any(|blk| match &blk.term {
            Term::Goto(t) => *t == b,
            Term::Switch { targets, otherwise, .. } => *otherwise == b || targets.iter().any(|x| x.1 == b),
            Term::Call { next, .. } | Term::Assert { next, .. } => *next == b,
            _ => false,
        })
    }

    /// The type an expression would have, for literals beside it; only for
    /// simple expressions that can be looked at without lowering.
    fn peek_type(&mut self, fb: &Fb, e: &ast::Expr) -> Option<TyId> {
        match &e.kind {
            E::Name(n) => {
                let v = fb.lookup(n)?;
                let p = self.var_place(fb, v);
                Some(self.place_ty(fb, &p))
            }
            E::Cast(_, t) => {
                let env = fb.env.clone();
                self.resolve_ty(t, &env).ok()
            }
            E::Field(b, f) => {
                let bt = self.peek_type(fb, b)?;
                let bt = self.types.pointee(bt).filter(|_| self.types.is_ref(bt) || self.types.is_ptr(bt)).unwrap_or(bt);
                let a = self.types.adt_of(bt)?;
                match &a.body {
                    types::AdtBody::Struct(fs) => fs.iter().find(|x| &x.name == f).map(|x| x.ty),
                    _ => None,
                }
            }
            E::Binary(op, a, _) if !op.is_compare() => self.peek_type(fb, a),
            E::Unary(ast::UnOp::Deref, a) => {
                let t = self.peek_type(fb, a)?;
                self.types.pointee(t)
            }
            E::Unary(ast::UnOp::Neg, a) => self.peek_type(fb, a),
            E::Index(b, _) => {
                let bt = self.peek_type(fb, b)?;
                match self.types.kind(bt).clone() {
                    TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::Ptr(e) => Some(e),
                    TyKind::Str => Some(types::U8),
                    TyKind::Adt(_) => {
                        let (fid, iargs) = self.find_method(bt, "index").ok()??;
                        let id = self.instance(fid, iargs, e.span).ok()?;
                        let r = self.out[id as usize].sig.ret;
                        self.types.pointee(r)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn name_expr(&mut self, fb: &mut Fb, n: &str, exp: Option<TyId>, span: Span) -> R<Val> {
        if let Some(v) = fb.lookup(n) {
            let p = self.var_place(fb, v);
            let t = self.place_ty(fb, &p);
            return Ok(Val::place(p, t));
        }
        if let Some(c) = fb.env.get(n).cloned() {
            return Ok(match c {
                CVal::Int(i) => {
                    let t = exp.filter(|&t| self.types.is_int(t)).unwrap_or(types::I64);
                    Val::op(Operand::Const(Const::Int(i, t)), t)
                }
                CVal::Bool(b) => Val::op(Operand::Const(Const::Bool(b)), types::BOOL),
                CVal::Type(_) => return ty_err(span, &format!("`{}` is a type, not a value", n)),
                CVal::Lambda(..) => return ty_err(span, "a compile-time closure can only be called"),
            });
        }
        if n == "null" {
            let t = match exp {
                Some(t) if self.types.is_ptr(t) => t,
                _ => return ty_err(span, "the type of `null` must be known: a pointer type is expected here"),
            };
            return Ok(Val::op(Operand::Const(Const::Null(t)), t));
        }
        let module = fb.env.module;
        match self.lookup(module, n) {
            Some(Sym::Const(c)) => {
                let (v, t) = self.const_value(c)?;
                Ok(Val::op(Operand::Const(v), t))
            }
            Some(Sym::Static(i)) => self.static_place(fb, i, span),
            Some(Sym::Fn(f)) => self.fn_value(f, Vec::new(), span),
            Some(_) => ty_err(span, &format!("`{}` is not a value", n)),
            None => {
                // A variant named alone: `None`, or one of the expected enum.
                if let Some(t) = self.variant_owner(exp, n, true)? {
                    return self.variant_value(fb, t, n, &[], span);
                }
                ty_err(span, &format!("unknown name `{}`", n))
            }
        }
    }

    /// The enum a bare variant name belongs to: the expected type's, or
    /// the prelude's `Option`/`Result` for `Some`, `None`, `Ok`, `Err`.
    pub fn variant_owner(&mut self, exp: Option<TyId>, n: &str, _unit: bool) -> R<Option<TyId>> {
        if let Some(t) = exp {
            if let Some(vs) = self.types.variants(t) {
                if vs.iter().any(|v| v.name == n) {
                    return Ok(Some(t));
                }
            }
        }
        Ok(None)
    }

    /// A `static` as a place, through its address.
    fn static_place(&mut self, fb: &mut Fb, i: u32, span: Span) -> R<Val> {
        if fb.unsafe_depth == 0 {
            return ty_err(span, "a `static` is shared by the whole program, so it is only used in `unsafe` code");
        }
        let (t, _) = self.static_info(i)?;
        let pt = self.types.ptr(t);
        let a = fb.temp(pt, span);
        fb.assign(Place::local(a), Rvalue::Use(Operand::Const(Const::Static(i, pt))), span);
        Ok(Val::place(Place::deref(a), t))
    }

    pub fn fn_value(&mut self, f: u32, args: Vec<CVal>, span: Span) -> R<Val> {
        let d = self.fns[f as usize].decl;
        if d.params.iter().any(|p| p.mode == Mode::Comptime) && args.is_empty() {
            return ty_err(span, "a generic function cannot be used as a value without its compile-time arguments");
        }
        let id = self.instance(f, args, span)?;
        let fun = &self.out[id as usize];
        if fun.pass.contains(&ParamPass::Owned) {
            return ty_err(span, "a function with `sink` parameters of non-plain types cannot be used as a `fnptr` yet");
        }
        let sig = fun.sig.clone();
        let t = self.types.intern(TyKind::FnPtr(sig));
        Ok(Val::op(Operand::Const(Const::Fn(id)), t))
    }

    fn auto_deref(&mut self, fb: &mut Fb, v: Val, span: Span) -> R<Val> {
        match self.types.kind(v.ty).clone() {
            TyKind::Ref(inner) | TyKind::RefMut(inner) => {
                let (p, _) = self.as_place(fb, v, span);
                Ok(Val::place(p.with(Proj::Deref), inner))
            }
            TyKind::Ptr(inner) => {
                if fb.unsafe_depth == 0 {
                    return ty_err(span, "reading through a pointer is only allowed in `unsafe` code");
                }
                let o = self.operand(fb, v, span)?;
                let tmp = match o {
                    Operand::Copy(p) if !p.proj.iter().any(|x| matches!(x, Proj::Index(_))) => p,
                    o => {
                        let t = fb.temp(self.types.ptr(inner), span);
                        fb.assign(Place::local(t), Rvalue::Use(o), span);
                        Place::local(t)
                    }
                };
                Ok(Val::place(tmp.with(Proj::Deref), inner))
            }
            _ => Ok(v),
        }
    }

    fn field_expr(&mut self, fb: &mut Fb, whole: &ast::Expr, base: &ast::Expr, name: &str, exp: Option<TyId>) -> R<Val> {
        let span = whole.span;
        // A path: `module.item`, `Type.Variant`, `Type.CONST`.
        if let Some(p) = expr_path(whole) {
            if fb.lookup(&p[0]).is_none() {
                if let Some(v) = self.path_value(fb, &p, exp, span)? {
                    return Ok(v);
                }
            }
        }
        if let E::Call(..) = &base.kind {
            let env = fb.env.clone();
            if let Some(t) = self.try_expr_ty(base, &env)? {
                return self.type_member(fb, t, name, &[], exp, span, false);
            }
        }
        let bv = self.expr(fb, base, None)?;
        self.field_of(fb, bv, name, span)
    }

    pub fn field_of(&mut self, fb: &mut Fb, bv: Val, name: &str, span: Span) -> R<Val> {
        let mut bv = self.auto_deref(fb, bv, span)?;
        for _ in 0..8 {
            if let Some(a) = self.types.adt_of(bv.ty) {
                if let types::AdtBody::Struct(fs) = &a.body {
                    if let Some(i) = fs.iter().position(|f| f.name == name) {
                        let f = &fs[i];
                        let ft = f.ty;
                        let decl_mod = self.adts[a.decl as usize].module;
                        if !f.public && !self.same_package(decl_mod, fb.env.module) {
                            return ty_err(span, &format!("the field `{}` of `{}` is private", name, a.name));
                        }
                        let temp = bv.temp;
                        let (p, _) = self.as_place(fb, bv, span);
                        return Ok(Val { vk: VK::Place(p.with(Proj::Field(i as u32))), ty: ft, temp });
                    }
                }
            }
            // `len` of views is a field; the rest are methods.
            if matches!(self.types.kind(bv.ty), TyKind::Str | TyKind::Slice(_)) && (name == "len" || name == "ptr") {
                let et = match self.types.kind(bv.ty) {
                    TyKind::Slice(e) => *e,
                    _ => types::U8,
                };
                let (p, _) = self.as_place(fb, bv, span);
                if name == "len" {
                    return Ok(Val::op(Operand::Copy(p.with(Proj::Field(1))), types::I64));
                }
                let pt = self.types.ptr(et);
                return Ok(Val::op(Operand::Copy(p.with(Proj::Field(0))), pt));
            }
            // Through `deref` (`deref_mut` for a place being changed).
            let wm = fb.want_mut;
            if wm && self.find_method(bv.ty, "deref_mut")?.is_some() && matches!(&bv.vk, VK::Place(p) if self.place_mutable(fb, p)) {
                fb.want_mut = false;
                bv = self.method_call_val(fb, bv, "deref_mut", vec![], span, None)?;
                fb.want_mut = wm;
                continue;
            }
            if self.find_method(bv.ty, "deref")?.is_some() {
                fb.want_mut = false;
                bv = self.method_call_val(fb, bv, "deref", vec![], span, None)?;
                fb.want_mut = wm;
                continue;
            }
            break;
        }
        ty_err(span, &format!("`{}` has no field `{}`", self.types.show(bv.ty), name))
    }

    /// A dotted path that names something other than a variable's field.
    fn path_value(&mut self, fb: &mut Fb, p: &[String], exp: Option<TyId>, span: Span) -> R<Option<Val>> {
        let env = fb.env.clone();
        // `Type.member`
        let (head, last) = p.split_at(p.len() - 1);
        if self.path_is_type(head, &env) {
            let t = self.resolve_path_ty_pub(head, &env, span)?;
            return self.type_member(fb, t, &last[0], &[], exp, span, false).map(Some);
        }
        // `Enum.Variant` with the enum's arguments inferred.
        if let Some((Sym::Adt(d), _)) = self.lookup_path(env.module, head) {
            let t = self.infer_enum(d, exp, &last[0], span)?;
            return self.variant_value(fb, t, &last[0], &[], span).map(Some);
        }
        match self.lookup_path(env.module, p) {
            Some((Sym::Const(c), _)) => {
                let (v, t) = self.const_value(c)?;
                Ok(Some(Val::op(Operand::Const(v), t)))
            }
            Some((Sym::Static(i), _)) => self.static_place(fb, i, span).map(Some),
            Some((Sym::Fn(f), _)) => self.fn_value(f, Vec::new(), span).map(Some),
            Some(_) => ty_err(span, &format!("`{}` is not a value", p.join("."))),
            None => Ok(None),
        }
    }

    pub fn resolve_path_ty_pub(&mut self, p: &[String], env: &Env, span: Span) -> R<TyId> {
        let t = ast::Ty { kind: ast::TyKind::Path(p.to_vec(), None), span };
        self.resolve_ty(&t, env)
    }

    /// The instance of a generic enum named without arguments: from the
    /// expected type.
    pub fn infer_enum(&mut self, d: u32, exp: Option<TyId>, _variant: &str, span: Span) -> R<TyId> {
        if let Some(t) = exp {
            if let Some(a) = self.types.adt_of(t) {
                if a.decl == d {
                    return Ok(t);
                }
            }
        }
        if self.adts[d as usize].params().is_empty() {
            return self.adt_instance(d, Vec::new(), span);
        }
        ty_err(span, &format!("the arguments of `{}` cannot be inferred here; write them: `{}(...)`", self.adts[d as usize].name, self.adts[d as usize].name))
    }

    /// `T.name` or `T.name(args)`: a variant, an associated function or a
    /// constant of a type.
    pub fn type_member(&mut self, fb: &mut Fb, t: TyId, name: &str, args: &[ast::Expr], _exp: Option<TyId>, span: Span, call: bool) -> R<Val> {
        if let Some(vs) = self.types.variants(t) {
            if vs.iter().any(|v| v.name == name) {
                return self.variant_value(fb, t, name, args, span);
            }
        }
        if let Some((fid, iargs)) = self.find_method(t, name)? {
            if !call {
                return ty_err(span, &format!("`{}.{}` is a function; call it", self.types.show(t), name));
            }
            return self.call_decl(fb, fid, iargs, None, args, span, _exp);
        }
        ty_err(span, &format!("`{}` has no variant or function `{}`", self.types.show(t), name))
    }

    /// `Vec.new()`, `Box.new(x)`, `Option.Some(x)`: a generic type named
    /// without arguments, which come from the expected type or the call.
    fn generic_static_call(&mut self, fb: &mut Fb, d: u32, name: &str, args: &[ast::Expr], exp: Option<TyId>, span: Span) -> R<Val> {
        if let Some(e) = exp {
            if self.types.adt_of(e).map(|a| a.decl == d).unwrap_or(false) {
                return self.type_member(fb, e, name, args, exp, span, true);
            }
        }
        if let AdtKind::Enum(en) = self.adts[d as usize].kind {
            if en.variants.iter().any(|v| v.name == name) {
                let t = self.infer_enum(d, exp, name, span)?;
                return self.variant_value(fb, t, name, args, span);
            }
        }
        let impls = self.adts[d as usize].impls.clone();
        for imp in impls {
            if let Some(&fid) = self.impls[imp as usize].fns.get(name) {
                return self.call_decl(fb, fid, Vec::new(), None, args, span, exp);
            }
        }
        ty_err(span, &format!("`{}` has no function `{}`", self.adts[d as usize].name, name))
    }

    pub fn variant_value(&mut self, fb: &mut Fb, t: TyId, name: &str, args: &[ast::Expr], span: Span) -> R<Val> {
        let vs = self.types.variants(t).unwrap().clone();
        let vi = vs.iter().position(|v| v.name == name).unwrap();
        let fields = vs[vi].fields.clone();
        if fields.len() != args.len() {
            return ty_err(span, &format!("`{}` takes {} value(s), {} given", name, fields.len(), args.len()));
        }
        let mut ops = Vec::new();
        for (a, ft) in args.iter().zip(fields) {
            let v = self.expr(fb, a, Some(ft))?;
            let v = self.coerce(fb, v, ft, a.span)?;
            ops.push(self.operand(fb, v, a.span)?);
        }
        Ok(self.rvalue(fb, Rvalue::Aggregate(Agg::Variant(t, vi as u32), ops), t, span))
    }

    fn struct_lit(&mut self, fb: &mut Fb, path: &ast::Expr, fields: &[(String, ast::Expr, Span)], exp: Option<TyId>, span: Span) -> R<Val> {
        let env = fb.env.clone();
        let t = match self.try_expr_ty(path, &env) {
            Ok(Some(t)) => t,
            r => {
                // A generic struct named without arguments: the expected type.
                let p = expr_path(path);
                let d = p.as_ref().and_then(|p| match self.lookup_path(env.module, p) {
                    Some((Sym::Adt(d), _)) => Some(d),
                    _ => None,
                });
                match (d, exp.and_then(|e| self.types.adt_of(e).map(|a| (a.decl, e)))) {
                    (Some(d), Some((ed, e))) if d == ed => e,
                    _ => {
                        r?;
                        return ty_err(path.span, "expected a struct name");
                    }
                }
            }
        };
        let Some(a) = self.types.adt_of(t) else { return ty_err(path.span, &format!("`{}` is not a struct", self.types.show(t))) };
        let types::AdtBody::Struct(fs) = a.body.clone() else { return ty_err(path.span, &format!("`{}` is not a struct", self.types.show(t))) };
        let decl_mod = self.adts[a.decl as usize].module;
        let mut vals: Vec<Option<Operand>> = vec![None; fs.len()];
        for (n, e, sp) in fields {
            let Some(i) = fs.iter().position(|f| &f.name == n) else {
                return ty_err(*sp, &format!("`{}` has no field `{}`", self.types.show(t), n));
            };
            if !fs[i].public && !self.same_package(decl_mod, fb.env.module) {
                return ty_err(*sp, &format!("the field `{}` is private", n));
            }
            if vals[i].is_some() {
                return ty_err(*sp, &format!("`{}` is given twice", n));
            }
            let v = self.expr(fb, e, Some(fs[i].ty))?;
            let v = self.coerce(fb, v, fs[i].ty, e.span)?;
            vals[i] = Some(self.operand(fb, v, e.span)?);
        }
        let mut ops = Vec::new();
        for (i, v) in vals.into_iter().enumerate() {
            match v {
                Some(o) => ops.push(o),
                None => return ty_err(span, &format!("the field `{}` is missing", fs[i].name)),
            }
        }
        Ok(self.rvalue(fb, Rvalue::Aggregate(Agg::Struct(t), ops), t, span))
    }

    fn index_expr(&mut self, fb: &mut Fb, base: &ast::Expr, idx: &ast::Expr, span: Span, write: bool) -> R<Val> {
        let bv = if write { self.expr_mut(fb, base)? } else { self.expr(fb, base, None)? };
        // A borrow held as a value (`ref Vec(T)`): what it points to.
        let bv = if self.types.is_ref(bv.ty) { self.auto_deref(fb, bv, span)? } else { bv };
        // Slicing: `xs[a..b]`.
        if let E::Range(lo, hi) = &idx.kind {
            return self.slice_expr(fb, bv, lo.as_deref(), hi.as_deref(), span);
        }
        match self.types.kind(bv.ty).clone() {
            TyKind::Array(et, n) => {
                let iv = self.expr(fb, idx, Some(types::I64))?;
                let iv = self.coerce(fb, iv, types::I64, idx.span)?;
                let io = self.operand(fb, iv, idx.span)?;
                let il = self.operand_local(fb, io, types::I64, span);
                self.bounds_check(fb, Operand::Copy(Place::local(il)), Operand::Const(Const::Int(n as i128, types::I64)), span);
                let temp = bv.temp;
                let (p, _) = self.as_place(fb, bv, span);
                Ok(Val { vk: VK::Place(p.with(Proj::Index(il))), ty: et, temp })
            }
            TyKind::Slice(et) | TyKind::Ptr(et) if !matches!(self.types.kind(bv.ty), TyKind::Ptr(_)) || fb.unsafe_depth > 0 => {
                let is_ptr = self.types.is_ptr(bv.ty);
                let iv = self.expr(fb, idx, Some(types::I64))?;
                let iv = self.coerce(fb, iv, types::I64, idx.span)?;
                let io = self.operand(fb, iv, idx.span)?;
                let pt = self.types.ptr(et);
                let (bp, _) = self.as_place(fb, bv, span);
                let data = if is_ptr { Operand::Copy(bp.clone()) } else { Operand::Copy(bp.with(Proj::Field(0))) };
                if !is_ptr {
                    let il = self.operand_local(fb, io.clone(), types::I64, span);
                    let len = Operand::Copy(self.place_of_view_len(fb, span, il, &bp));
                    self.bounds_check(fb, Operand::Copy(Place::local(il)), len, span);
                    let a = self.rvalue(fb, Rvalue::Offset(data, Operand::Copy(Place::local(il))), pt, span);
                    let ap = self.place_of_val(a);
                    return Ok(Val::place(ap.with(Proj::Deref), et));
                }
                let a = self.rvalue(fb, Rvalue::Offset(data, io), pt, span);
                let ap = self.place_of_val(a);
                Ok(Val::place(ap.with(Proj::Deref), et))
            }
            TyKind::Ptr(_) => ty_err(span, "indexing a pointer is only allowed in `unsafe` code"),
            TyKind::Str => {
                let iv = self.expr(fb, idx, Some(types::I64))?;
                let iv = self.coerce(fb, iv, types::I64, idx.span)?;
                let io = self.operand(fb, iv, idx.span)?;
                let il = self.operand_local(fb, io, types::I64, span);
                let (bp, _) = self.as_place(fb, bv, span);
                let len = Operand::Copy(bp.with(Proj::Field(1)));
                self.bounds_check(fb, Operand::Copy(Place::local(il)), len, span);
                let pt = self.types.ptr(types::U8);
                let a = self.rvalue(fb, Rvalue::Offset(Operand::Copy(bp.with(Proj::Field(0))), Operand::Copy(Place::local(il))), pt, span);
                let ap = self.place_of_val(a);
                // Bytes of a `str` are read only.
                let v = Operand::Copy(ap.with(Proj::Deref));
                Ok(self.rvalue(fb, Rvalue::Use(v), types::U8, span))
            }
            TyKind::Adt(_) => {
                // `index`/`index_mut` projections.
                let mutable = write && matches!(&bv.vk, VK::Place(p) if self.place_mutable(fb, p)) && !bv.temp;
                let name = if mutable && self.find_method(bv.ty, "index_mut")?.is_some() { "index_mut" } else { "index" };
                if self.find_method(bv.ty, name)?.is_none() {
                    return ty_err(span, &format!("`{}` cannot be indexed (it has no `index` method)", self.types.show(bv.ty)));
                }
                self.method_call(fb, bv, name, std::slice::from_ref(idx), span, None, false)
            }
            _ => ty_err(span, &format!("`{}` cannot be indexed", self.types.show(bv.ty))),
        }
    }

    fn place_of_view_len(&mut self, _fb: &mut Fb, _span: Span, _il: Local, bp: &Place) -> Place {
        bp.with(Proj::Field(1))
    }

    /// Puts an operand in a local, so it can be used twice.
    pub fn operand_local(&mut self, fb: &mut Fb, o: Operand, t: TyId, span: Span) -> Local {
        if let Operand::Copy(p) = &o {
            if p.proj.is_empty() && !fb.body.locals[p.local as usize].mutable {
                return p.local;
            }
        }
        let l = fb.temp(t, span);
        fb.assign(Place::local(l), Rvalue::Use(o), span);
        l
    }

    pub fn bounds_check(&mut self, fb: &mut Fb, i: Operand, len: Operand, span: Span) {
        // An unsigned comparison checks `0 <= i < len` at once.
        let c = fb.temp(types::BOOL, span);
        let ui = fb.temp(types::U64, span);
        let ul = fb.temp(types::U64, span);
        fb.assign(Place::local(ui), Rvalue::Cast(i, types::U64, CastKind::Numeric), span);
        fb.assign(Place::local(ul), Rvalue::Cast(len, types::U64, CastKind::Numeric), span);
        fb.assign(Place::local(c), Rvalue::Bin(Op::Lt, Operand::Copy(Place::local(ui)), Operand::Copy(Place::local(ul))), span);
        let next = fb.new_block();
        fb.term(Term::Assert { cond: Operand::Copy(Place::local(c)), msg: "index out of bounds".into(), next, span });
        fb.switch_to(next);
    }

    fn slice_expr(&mut self, fb: &mut Fb, bv: Val, lo: Option<&ast::Expr>, hi: Option<&ast::Expr>, span: Span) -> R<Val> {
        let bt = bv.ty;
        let (elem, view) = match self.types.kind(bt).clone() {
            TyKind::Str => (types::U8, types::STR),
            TyKind::Slice(e) => (e, bt),
            TyKind::Array(e, _) => {
                let st = self.view_ty(TyKind::Slice(e));
                (e, st)
            }
            TyKind::Adt(_) => {
                // `as_slice`/`as_str`, then slice that.
                let name = if self.find_method(bt, "as_str")?.is_some() { "as_str" } else { "as_slice" };
                if self.find_method(bt, name)?.is_none() {
                    return ty_err(span, &format!("`{}` cannot be sliced", self.types.show(bt)));
                }
                let v = self.method_call_val(fb, bv, name, vec![], span, None)?;
                return self.slice_expr(fb, v, lo, hi, span);
            }
            _ => return ty_err(span, &format!("`{}` cannot be sliced", self.types.show(bt))),
        };
        let bv = if let TyKind::Array(..) = self.types.kind(bt) { self.coerce(fb, bv, view, span)? } else { bv };
        let (bp, _) = self.as_place(fb, bv, span);
        let len = Operand::Copy(bp.with(Proj::Field(1)));
        let lo_o = match lo {
            Some(e) => {
                let v = self.expr(fb, e, Some(types::I64))?;
                let v = self.coerce(fb, v, types::I64, e.span)?;
                self.operand(fb, v, e.span)?
            }
            None => Operand::Const(Const::Int(0, types::I64)),
        };
        let hi_o = match hi {
            Some(e) => {
                let v = self.expr(fb, e, Some(types::I64))?;
                let v = self.coerce(fb, v, types::I64, e.span)?;
                self.operand(fb, v, e.span)?
            }
            None => len.clone(),
        };
        let lo_l = self.operand_local(fb, lo_o, types::I64, span);
        let hi_l = self.operand_local(fb, hi_o, types::I64, span);
        // 0 <= lo <= hi <= len
        let lenp1 = fb.temp(types::I64, span);
        fb.assign(Place::local(lenp1), Rvalue::Bin(Op::Add, len.clone(), Operand::Const(Const::Int(1, types::I64))), span);
        self.bounds_check(fb, Operand::Copy(Place::local(hi_l)), Operand::Copy(Place::local(lenp1)), span);
        let hip1 = fb.temp(types::I64, span);
        fb.assign(Place::local(hip1), Rvalue::Bin(Op::Add, Operand::Copy(Place::local(hi_l)), Operand::Const(Const::Int(1, types::I64))), span);
        self.bounds_check(fb, Operand::Copy(Place::local(lo_l)), Operand::Copy(Place::local(hip1)), span);
        let pt = self.types.ptr(elem);
        let data = self.rvalue(fb, Rvalue::Offset(Operand::Copy(bp.with(Proj::Field(0))), Operand::Copy(Place::local(lo_l))), pt, span);
        let n = fb.temp(types::I64, span);
        fb.assign(Place::local(n), Rvalue::Bin(Op::Sub, Operand::Copy(Place::local(hi_l)), Operand::Copy(Place::local(lo_l))), span);
        let dp = self.place_of_val(data);
        Ok(self.rvalue(fb, Rvalue::Aggregate(Agg::View(view), vec![Operand::Copy(dp), Operand::Copy(Place::local(n))]), view, span))
    }

    fn unary_expr(&mut self, fb: &mut Fb, op: ast::UnOp, inner: &ast::Expr, exp: Option<TyId>, span: Span) -> R<Val> {
        match op {
            ast::UnOp::Neg => {
                if let E::Int(v) = &inner.kind {
                    // `-128` fits in an i8 although 128 does not.
                    let t = exp.filter(|&t| self.types.is_int(t) || self.types.is_float(t)).unwrap_or(types::I64);
                    if self.types.is_float(t) {
                        return Ok(Val::op(Operand::Const(Const::Float(-(*v as f64), t)), t));
                    }
                    let n = -(*v as i128);
                    if !self.int_fits(n, t) {
                        return ty_err(span, &format!("-{} does not fit in `{}`", v, self.types.show(t)));
                    }
                    return Ok(Val::op(Operand::Const(Const::Int(n, t)), t));
                }
                let v = self.expr(fb, inner, exp)?;
                let t = v.ty;
                let ok = self.types.int(t).map(|i| i.signed).unwrap_or(false) || self.types.is_float(t);
                if !ok {
                    return ty_err(span, &format!("`-` needs a signed integer or a float, found `{}`", self.types.show(t)));
                }
                let o = self.operand(fb, v, span)?;
                Ok(self.rvalue(fb, Rvalue::Un(UnOp::Neg, o), t, span))
            }
            ast::UnOp::Not => {
                let v = self.expr(fb, inner, exp)?;
                let t = v.ty;
                if t != types::BOOL && !self.types.is_int(t) {
                    return ty_err(span, &format!("`!` needs a bool or an integer, found `{}`", self.types.show(t)));
                }
                let o = self.operand(fb, v, span)?;
                Ok(self.rvalue(fb, Rvalue::Un(UnOp::Not, o), t, span))
            }
            ast::UnOp::Deref => {
                let v = self.expr(fb, inner, None)?;
                match self.types.kind(v.ty).clone() {
                    TyKind::Ptr(_) => self.auto_deref(fb, v, span),
                    TyKind::Adt(_) if self.find_method(v.ty, "deref")?.is_some() => self.method_call_val(fb, v, "deref", vec![], span, None),
                    _ => ty_err(span, &format!("`*` needs a pointer, found `{}`", self.types.show(v.ty))),
                }
            }
            ast::UnOp::Addr => {
                // The address of a place, as a raw pointer.
                let v = self.expr(fb, inner, None)?;
                let t = v.ty;
                if let VK::Place(p) = &v.vk {
                    if !v.temp {
                        let pt = self.types.ptr(t);
                        let p = p.clone();
                        return Ok(self.rvalue(fb, Rvalue::Addr(p), pt, span));
                    }
                }
                ty_err(span, "`&` takes the address of a place (a variable, a field, an element)")
            }
        }
    }

    fn logic(&mut self, fb: &mut Fb, op: Op, a: &ast::Expr, b: &ast::Expr, span: Span) -> R<Val> {
        let r = fb.temp(types::BOOL, span);
        let av = self.expr(fb, a, Some(types::BOOL))?;
        let av = self.coerce(fb, av, types::BOOL, a.span)?;
        let ao = self.operand(fb, av, a.span)?;
        fb.assign(Place::local(r), Rvalue::Use(ao.clone()), span);
        let rhs = fb.new_block();
        let done = fb.new_block();
        let (t, f) = if op == Op::LogAnd { (rhs, done) } else { (done, rhs) };
        fb.term(Term::Switch { discr: ao, targets: vec![(0, f)], otherwise: t });
        fb.switch_to(rhs);
        fb.push_scope(true);
        let bv = self.expr(fb, b, Some(types::BOOL))?;
        let bv = self.coerce(fb, bv, types::BOOL, b.span)?;
        let bo = self.operand(fb, bv, b.span)?;
        fb.assign(Place::local(r), Rvalue::Use(bo), span);
        self.pop_scope(fb);
        fb.goto(done);
        Ok(Val::op(Operand::Copy(Place::local(r)), types::BOOL))
    }

    /// A value as an operand in a temporary, so that what is lowered next
    /// cannot change it.
    fn value_operand_val(&mut self, fb: &mut Fb, v: Val, span: Span) -> R<Val> {
        match &v.vk {
            VK::Op(Operand::Const(_)) => Ok(v),
            VK::Place(_) if v.temp => Ok(v),
            _ => {
                let t = v.ty;
                let o = self.operand(fb, v, span)?;
                let l = fb.temp(t, span);
                fb.assign(Place::local(l), Rvalue::Use(o), span);
                Ok(Val { vk: VK::Place(Place::local(l)), ty: t, temp: true })
            }
        }
    }

    fn peek_is_adt(&mut self, fb: &Fb, e: &ast::Expr) -> bool {
        match self.peek_type(fb, e) {
            Some(t) => self.types.adt_of(t).is_some(),
            // Unknown: take the general path.
            None => true,
        }
    }

    /// A binary operation on two values already lowered (numbers).
    fn binary_vals(&mut self, fb: &mut Fb, op: Op, av: Val, bv: Val, span: Span) -> R<Val> {
        let at = av.ty;
        let bv = if bv.ty != at && !matches!(op, Op::Shl | Op::Shr) {
            match &bv.vk {
                VK::Op(Operand::Const(Const::Int(v, _))) if self.types.is_int(at) && self.int_fits(*v, at) => Val::op(Operand::Const(Const::Int(*v, at)), at),
                VK::Op(Operand::Const(Const::Int(v, _))) if self.types.is_float(at) => Val::op(Operand::Const(Const::Float(*v as f64, at)), at),
                _ => bv,
            }
        } else {
            bv
        };
        let bt = bv.ty;
        let ok = (self.types.is_int(at) || self.types.is_float(at)) && (at == bt || (matches!(op, Op::Shl | Op::Shr) && self.types.is_int(bt)));
        let ok = ok || (at == types::BOOL && bt == types::BOOL && matches!(op, Op::And | Op::Or | Op::Xor));
        if !ok {
            return self.op_err(op, at, bt, span);
        }
        if self.types.is_float(at) && matches!(op, Op::And | Op::Or | Op::Xor | Op::Shl | Op::Shr | Op::AddWrap | Op::SubWrap | Op::MulWrap) {
            return self.op_err(op, at, bt, span);
        }
        let ao = self.operand(fb, av, span)?;
        let mut bo = self.operand(fb, bv, span)?;
        if matches!(op, Op::Shl | Op::Shr) && bt != at {
            let c = self.rvalue(fb, Rvalue::Cast(bo, at, CastKind::Numeric), at, span);
            bo = Operand::Copy(self.place_of_val(c));
        }
        Ok(self.rvalue(fb, Rvalue::Bin(op, ao, bo), at, span))
    }

    pub fn binary_on(&mut self, fb: &mut Fb, op: Op, av: Val, b: &ast::Expr, span: Span) -> R<Val> {
        let at = av.ty;
        // Operators on library types call their methods.
        if self.types.adt_of(at).is_some() || at == types::STR || matches!(self.types.kind(at), TyKind::Slice(_) | TyKind::Tuple(_)) && at != types::UNIT {
            return self.operator_method(fb, op, av, b, span);
        }
        let bexp = if matches!(op, Op::Shl | Op::Shr) { None } else { Some(at) };
        let bv = self.expr(fb, b, bexp)?;
        let bt = bv.ty;
        let ok_num = |s: &Self, t: TyId| s.types.is_int(t) || s.types.is_float(t);
        let rt = match op {
            Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Rem => {
                if self.types.is_ptr(at) && matches!(op, Op::Add | Op::Sub) && self.types.is_int(bt) {
                    if fb.unsafe_depth == 0 {
                        return ty_err(span, "pointer arithmetic is only allowed in `unsafe` code");
                    }
                    let ao = self.operand(fb, av, span)?;
                    let mut bo = self.operand(fb, bv, span)?;
                    if bt != types::I64 {
                        let c = self.rvalue(fb, Rvalue::Cast(bo, types::I64, CastKind::Numeric), types::I64, span);
                        bo = Operand::Copy(self.place_of_val(c));
                    }
                    if op == Op::Sub {
                        let n = self.rvalue(fb, Rvalue::Un(UnOp::Neg, bo), types::I64, span);
                        bo = Operand::Copy(self.place_of_val(n));
                    }
                    return Ok(self.rvalue(fb, Rvalue::Offset(ao, bo), at, span));
                }
                if !ok_num(self, at) || at != bt {
                    return self.op_err(op, at, bt, span);
                }
                at
            }
            Op::AddWrap | Op::SubWrap | Op::MulWrap | Op::And | Op::Or | Op::Xor => {
                if (at == types::BOOL && matches!(op, Op::And | Op::Or | Op::Xor)) && bt == types::BOOL {
                    at
                } else if !self.types.is_int(at) || at != bt {
                    return self.op_err(op, at, bt, span);
                } else {
                    at
                }
            }
            Op::Shl | Op::Shr => {
                if !self.types.is_int(at) || !self.types.is_int(bt) {
                    return self.op_err(op, at, bt, span);
                }
                at
            }
            Op::Eq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge => {
                let comparable = ok_num(self, at) || at == types::BOOL || self.types.is_ptr(at) || matches!(self.types.kind(at), TyKind::FnPtr(_));
                if !comparable || at != bt {
                    return self.op_err(op, at, bt, span);
                }
                if at == types::BOOL && !matches!(op, Op::Eq | Op::Ne) {
                    return self.op_err(op, at, bt, span);
                }
                types::BOOL
            }
            Op::LogAnd | Op::LogOr => unreachable!(),
        };
        let ao = self.operand(fb, av, span)?;
        let mut bo = self.operand(fb, bv, b.span)?;
        if matches!(op, Op::Shl | Op::Shr) && bt != at {
            let c = self.rvalue(fb, Rvalue::Cast(bo, at, CastKind::Numeric), at, span);
            bo = Operand::Copy(self.place_of_val(c));
        }
        if matches!(op, Op::Rem) && self.types.is_float(at) {
            // fine: fmod
        }
        Ok(self.rvalue(fb, Rvalue::Bin(op, ao, bo), rt, span))
    }

    fn op_err<T>(&self, op: Op, a: TyId, b: TyId, span: Span) -> R<T> {
        if a == b {
            ty_err(span, &format!("`{}` is not defined for `{}`", op.text(), self.types.show(a)))
        } else {
            ty_err(span, &format!("`{}` needs both sides of the same type, found `{}` and `{}`", op.text(), self.types.show(a), self.types.show(b)))
        }
    }

    /// `==` calls `eq`, `<` and friends call `compare`, `+` calls `add`.
    fn operator_method(&mut self, fb: &mut Fb, op: Op, av: Val, b: &ast::Expr, span: Span) -> R<Val> {
        let at = av.ty;
        let (name, post) = match op {
            Op::Eq => ("eq", 0),
            Op::Ne => ("eq", 1),
            Op::Lt => ("compare", 2),
            Op::Le => ("compare", 3),
            Op::Gt => ("compare", 4),
            Op::Ge => ("compare", 5),
            Op::Add => ("add", 0),
            Op::Sub => ("sub", 0),
            Op::Mul => ("mul", 0),
            _ => return ty_err(span, &format!("`{}` is not defined for `{}`", op.text(), self.types.show(at))),
        };
        // `s + "x"` with `s` a `String` that cannot be moved (it is borrowed,
        // or used again): add to its text instead, making a new `String`.
        if op == Op::Add {
            if let VK::Place(p) = &av.vk {
                let movable = av.temp || self.place_movable(fb, p).is_ok();
                if !movable && self.find_method(at, "as_str")?.is_some() {
                    let s = self.method_call_val(fb, av, "as_str", vec![], span, None)?;
                    return self.method_call(fb, s, "add", std::slice::from_ref(b), span, None, false);
                }
            }
        }
        if self.find_method(at, name)?.is_none() {
            let tr = if name == "eq" { "Eq" } else if name == "compare" { "Ord" } else { name };
            return ty_err(span, &format!("`{}` needs `{}` to implement `{}`", op.text(), self.types.show(at), tr));
        }
        let r = self.method_call(fb, av, name, std::slice::from_ref(b), span, None, false)?;
        match post {
            0 => Ok(r),
            1 => {
                let o = self.operand(fb, r, span)?;
                Ok(self.rvalue(fb, Rvalue::Un(UnOp::Not, o), types::BOOL, span))
            }
            _ => {
                // `compare` returns an `Ordering`: Less, Equal, Greater.
                let (p, _) = self.as_place(fb, r, span);
                let d = self.rvalue(fb, Rvalue::Discriminant(p), types::I64, span);
                let dp = self.place_of_val(d);
                let (bop, k) = match post {
                    2 => (Op::Eq, 0),
                    3 => (Op::Ne, 2),
                    4 => (Op::Eq, 2),
                    _ => (Op::Ne, 0),
                };
                Ok(self.rvalue(fb, Rvalue::Bin(bop, Operand::Copy(dp), Operand::Const(Const::Int(k, types::I64))), types::BOOL, span))
            }
        }
    }

    fn cast(&mut self, fb: &mut Fb, inner: &ast::Expr, to: TyId, span: Span) -> R<Val> {
        let v = self.expr(fb, inner, if self.types.is_int(to) || self.types.is_float(to) { None } else { Some(to) })?;
        let from = v.ty;
        if from == to {
            return Ok(v);
        }
        let fk = self.types.kind(from).clone();
        let tk = self.types.kind(to).clone();
        let kind = match (&fk, &tk) {
            (TyKind::Int(_) | TyKind::Float(_), TyKind::Int(_) | TyKind::Float(_)) => CastKind::Numeric,
            (TyKind::Bool, TyKind::Int(_)) => CastKind::Numeric,
            (TyKind::Ptr(_), TyKind::Ptr(_)) => CastKind::Ptr,
            (TyKind::Ptr(_) | TyKind::FnPtr(_), TyKind::Int(i)) | (TyKind::Int(i), TyKind::Ptr(_) | TyKind::FnPtr(_)) if i.bits == 64 => {
                CastKind::Numeric
            }
            (TyKind::Ptr(_), TyKind::FnPtr(_)) | (TyKind::FnPtr(_), TyKind::Ptr(_)) => CastKind::Ptr,
            (TyKind::Adt(_), TyKind::Int(_)) if self.types.variants(from).map(|vs| vs.iter().all(|v| v.fields.is_empty())).unwrap_or(false) => {
                let (p, _) = self.as_place(fb, v, span);
                let d = self.rvalue(fb, Rvalue::Discriminant(p), types::I64, span);
                let dp = self.place_of_val(d);
                return Ok(self.rvalue(fb, Rvalue::Cast(Operand::Copy(dp), to, CastKind::Numeric), to, span));
            }
            _ => return ty_err(span, &format!("cannot convert `{}` to `{}` with `as`", self.types.show(from), self.types.show(to))),
        };
        let o = self.operand(fb, v, span)?;
        Ok(self.rvalue(fb, Rvalue::Cast(o, to, kind), to, span))
    }

    fn if_expr(&mut self, fb: &mut Fb, c: &ast::Expr, then: &ast::Block, els: Option<&ast::Expr>, exp: Option<TyId>, span: Span) -> R<Val> {
        let cv = self.expr(fb, c, Some(types::BOOL))?;
        let cv = self.coerce(fb, cv, types::BOOL, c.span)?;
        let co = self.operand(fb, cv, c.span)?;
        let tb = fb.new_block();
        let eb = fb.new_block();
        let done = fb.new_block();
        let want = els.is_some() && exp != Some(types::UNIT);
        // The result goes in a temporary of the statement around the `if`.
        let result = if want {
            let r = fb.new_local(types::UNIT, None, true, LocalKind::Temp, span);
            fb.add_temp_local(r);
            Some(r)
        } else {
            None
        };
        fb.term(Term::Switch { discr: co, targets: vec![(0, eb)], otherwise: tb });
        fb.switch_to(tb);
        let tv = self.block(fb, then, if want { exp } else { Some(types::UNIT) }, want)?;
        let mut rty = if tv.ty == types::NEVER { None } else { Some(tv.ty) };
        if let Some(r) = result {
            if tv.ty != types::NEVER && tv.ty != types::UNIT {
                fb.body.locals[r as usize].ty = tv.ty;
                let o = self.operand(fb, tv, then.span)?;
                fb.assign(Place::local(r), Rvalue::Use(o), span);
            }
        }
        fb.goto(done);
        fb.switch_to(eb);
        let mut ety = None;
        if let Some(e) = els {
            let ev = self.expr(fb, e, if want { rty.or(exp) } else { Some(types::UNIT) })?;
            let ev = match (want, rty) {
                (true, Some(t)) => self.coerce(fb, ev, t, e.span)?,
                _ => ev,
            };
            ety = if ev.ty == types::NEVER { None } else { Some(ev.ty) };
            if let Some(r) = result {
                if ev.ty != types::NEVER && ev.ty != types::UNIT {
                    fb.body.locals[r as usize].ty = ev.ty;
                    let o = self.operand(fb, ev, e.span)?;
                    fb.assign(Place::local(r), Rvalue::Use(o), span);
                }
            } else {
                self.discard(fb, ev, e.span)?;
            }
        }
        fb.goto(done);
        if rty.is_none() {
            rty = ety;
        }
        let Some(r) = result else {
            if els.is_some() && rty.is_none() {
                return Ok(Val::never());
            }
            return Ok(Val::unit());
        };
        let t = match rty {
            None => return Ok(Val::never()),
            Some(t) => t,
        };
        if t == types::UNIT {
            return Ok(Val::unit());
        }
        // Register the result where the statement's temporaries are.
        fb.body.locals[r as usize].ty = t;
        Ok(Val { vk: VK::Place(Place::local(r)), ty: t, temp: true })
    }

    fn try_expr(&mut self, fb: &mut Fb, inner: &ast::Expr, span: Span) -> R<Val> {
        let v = self.expr(fb, inner, None)?;
        let t = v.ty;
        let Some(a) = self.types.adt_of(t) else { return ty_err(span, &format!("`?` needs an `Option` or a `Result`, found `{}`", self.types.show(t))) };
        let decl = a.decl;
        let is_opt = Some(decl) == self.lang.option;
        let is_res = Some(decl) == self.lang.result;
        if !is_opt && !is_res {
            return ty_err(span, &format!("`?` needs an `Option` or a `Result`, found `{}`", self.types.show(t)));
        }
        let vs = self.types.variants(t).unwrap().clone();
        let (ok_name, err_name) = if is_opt { ("Some", "None") } else { ("Ok", "Err") };
        let ok = vs.iter().position(|v| v.name == ok_name).unwrap() as u32;
        let err = vs.iter().position(|v| v.name == err_name).unwrap() as u32;
        let ret_ty = fb.ty_of(RET);
        let rd = self.types.adt_of(ret_ty).map(|a| a.decl);
        if rd != Some(decl) || fb.ret_mode != RetMode::Value {
            return ty_err(span, &format!("`?` returns early with the `{}`, so the function must return an `{}`", err_name, if is_opt { "Option" } else { "Result" }));
        }
        // Own the value, then switch on it.
        let o = self.operand(fb, v, span)?;
        let tmp = fb.temp(t, span);
        fb.assign(Place::local(tmp), Rvalue::Use(o), span);
        let d = self.rvalue(fb, Rvalue::Discriminant(Place::local(tmp)), types::I64, span);
        let dp = self.place_of_val(d);
        let okb = fb.new_block();
        let errb = fb.new_block();
        fb.term(Term::Switch { discr: Operand::Copy(dp), targets: vec![(ok as i128, okb)], otherwise: errb });
        fb.switch_to(errb);
        let rvs = self.types.variants(ret_ty).unwrap().clone();
        let rerr = rvs.iter().position(|v| v.name == err_name).unwrap() as u32;
        let payload = if is_res {
            let et = vs[err as usize].fields[0];
            let rt = rvs[rerr as usize].fields[0];
            if et != rt {
                return ty_err(span, &format!("the error is `{}` but the function returns errors of type `{}`", self.types.show(et), self.types.show(rt)));
            }
            vec![Operand::Move(Place::local(tmp).with(Proj::Variant(err)).with(Proj::Field(0)))]
        } else {
            vec![]
        };
        fb.assign(Place::local(RET), Rvalue::Aggregate(Agg::Variant(ret_ty, rerr), payload), span);
        fb.push(Stmt::Forget(tmp));
        self.exit_to(fb, 0);
        fb.term(Term::Return);
        fb.switch_to(okb);
        let pt = vs[ok as usize].fields.first().copied().unwrap_or(types::UNIT);
        let out = fb.temp(pt, span);
        if !vs[ok as usize].fields.is_empty() {
            fb.assign(Place::local(out), Rvalue::Use(Operand::Move(Place::local(tmp).with(Proj::Variant(ok)).with(Proj::Field(0)))), span);
        }
        fb.push(Stmt::Forget(tmp));
        Ok(Val { vk: VK::Place(Place::local(out)), ty: pt, temp: true })
    }

    // ---- calls ----

    fn call_expr(&mut self, fb: &mut Fb, callee: &ast::Expr, args: &[ast::Expr], exp: Option<TyId>, span: Span) -> R<Val> {
        let env = fb.env.clone();
        match &callee.kind {
            E::Name(n) => {
                if let Some(v) = fb.lookup(n) {
                    let p = self.var_place(fb, v);
                    let t = self.place_ty(fb, &p);
                    return self.call_value(fb, Val::place(p, t), args, span);
                }
                if let Some((_, _, l, lf)) = self.comptime_closures.iter().find(|c| c.0 == fb.id && c.1 == *n).cloned() {
                    return self.call_comptime_closure(fb, l, lf, args, span);
                }
                if env.get(n).is_some() {
                    return ty_err(callee.span, &format!("`{}` is not a function", n));
                }
                match self.lookup(env.module, n) {
                    Some(Sym::Fn(f)) => return self.call_decl(fb, f, Vec::new(), None, args, span, exp),
                    Some(Sym::Adt(_)) => {
                        return ty_err(span, &format!("`{}(...)` is a type; build a value with `{} {{ ... }}` or call one of its functions", n, n))
                    }
                    Some(_) => return ty_err(callee.span, &format!("`{}` is not a function", n)),
                    None => {}
                }
                if let Some(v) = self.builtin_call(fb, n, args, exp, span)? {
                    return Ok(v);
                }
                if let Some(t) = self.variant_owner(exp, n, false)? {
                    return self.variant_value(fb, t, n, args, span);
                }
                // `Some(x)`, `Ok(x)` without an expected type: infer from x.
                if let Some(v) = self.prelude_variant(fb, n, args, span)? {
                    return Ok(v);
                }
                ty_err(callee.span, &format!("unknown function `{}`", n))
            }
            E::Field(base, name) => {
                // `module.f(...)`, `Type.f(...)`, `Enum.Variant(...)`
                if let Some(p) = expr_path(callee) {
                    // `T.f(...)`, with `T` a compile-time type parameter.
                    if p.len() == 2 && fb.lookup(&p[0]).is_none() && matches!(env.get(&p[0]), Some(CVal::Type(_))) {
                        let t = self.resolve_path_ty_pub(&p[..1], &env, span)?;
                        return self.type_member(fb, t, name, args, exp, span, true);
                    }
                    if fb.lookup(&p[0]).is_none() && env.get(&p[0]).is_none() {
                        let (head, _) = p.split_at(p.len() - 1);
                        if let Some((Sym::Fn(f), _)) = self.lookup_path(env.module, &p).filter(|_| p.len() > 1) {
                            return self.call_decl(fb, f, Vec::new(), None, args, span, exp);
                        }
                        if let Some((Sym::Adt(d), _)) = self.lookup_path(env.module, head) {
                            if !self.adts[d as usize].params().is_empty() && !(head.len() == 1 && env.get(&head[0]).is_some()) {
                                return self.generic_static_call(fb, d, name, args, exp, span);
                            }
                        }
                        if self.path_is_type(head, &env) {
                            let t = self.resolve_path_ty_pub(head, &env, span)?;
                            return self.type_member(fb, t, name, args, exp, span, true);
                        }
                        if let Some((Sym::Adt(d), _)) = self.lookup_path(env.module, head) {
                            let t = self.infer_enum(d, exp, name, span)?;
                            return self.type_member(fb, t, name, args, exp, span, true);
                        }
                    }
                }
                if p_is_type_call(base) {
                    if let Some(t) = self.try_expr_ty(base, &env)? {
                        return self.type_member(fb, t, name, args, exp, span, true);
                    }
                }
                // A method call; a receiver passed `inout` is lowered as a
                // place to change.
                let recv = if self.method_name_inout(name) { self.expr_mut(fb, base)? } else { self.expr(fb, base, None)? };
                // A field holding a function value is called as one.
                if let Some(a) = self.types.adt_of(recv.ty) {
                    if let types::AdtBody::Struct(fs) = &a.body {
                        if fs.iter().any(|f| &f.name == name) && self.find_method(recv.ty, name)?.is_none() {
                            let fv = self.field_of(fb, recv, name, span)?;
                            return self.call_value(fb, fv, args, span);
                        }
                    }
                }
                self.method_call(fb, recv, name, args, span, exp, false)
            }
            _ => {
                if let Some(t) = self.try_expr_ty(callee, &env)? {
                    return ty_err(span, &format!("`{}` is a type, not a function", self.types.show(t)));
                }
                let v = self.expr(fb, callee, None)?;
                self.call_value(fb, v, args, span)
            }
        }
    }

    fn prelude_variant(&mut self, fb: &mut Fb, n: &str, args: &[ast::Expr], span: Span) -> R<Option<Val>> {
        let decl = match n {
            "Some" | "None" => self.lang.option,
            "Ok" | "Err" => self.lang.result,
            _ => None,
        };
        let Some(d) = decl else { return Ok(None) };
        if n == "Some" && args.len() == 1 {
            let v = self.expr(fb, &args[0], None)?;
            let t = self.adt_instance(d, vec![CVal::Type(v.ty)], span)?;
            let o = self.operand(fb, v, span)?;
            let vi = self.types.variants(t).unwrap().iter().position(|x| x.name == "Some").unwrap();
            return Ok(Some(self.rvalue(fb, Rvalue::Aggregate(Agg::Variant(t, vi as u32), vec![o]), t, span)));
        }
        ty_err(span, &format!("the type of `{}` must be known here; write its type", n))
    }

    /// Calls a value: a `fnptr` or a closure.
    fn call_value(&mut self, fb: &mut Fb, v: Val, args: &[ast::Expr], span: Span) -> R<Val> {
        let (sig, closure) = match self.types.kind(v.ty).clone() {
            TyKind::FnPtr(s) => (s, false),
            TyKind::Closure(s) => (s, true),
            _ => return ty_err(span, &format!("`{}` is not a function", self.types.show(v.ty))),
        };
        if sig.params.len() != args.len() {
            return ty_err(span, &format!("this function takes {} argument(s), {} given", sig.params.len(), args.len()));
        }
        let mut ops = Vec::new();
        let callee_op = self.operand(fb, v, span)?;
        let ct = self.types.intern(if closure { TyKind::Closure(sig.clone()) } else { TyKind::FnPtr(sig.clone()) });
        let cl = self.operand_local(fb, callee_op, ct, span);
        for (a, &pt) in args.iter().zip(&sig.params) {
            ops.push(self.arg_for_local_ty(fb, a, pt)?);
        }
        let callee = if closure { Callee::Closure(Operand::Copy(Place::local(cl))) } else { Callee::Ptr(Operand::Copy(Place::local(cl))) };
        self.emit_call(fb, callee, ops, sig.ret, span)
    }

    /// An argument for a parameter whose lowered type is known (closures).
    fn arg_for_local_ty(&mut self, fb: &mut Fb, a: &ast::Expr, pt: TyId) -> R<Operand> {
        match self.types.kind(pt).clone() {
            TyKind::RefMut(inner) => {
                let (p, t) = self.mut_place(fb, a)?;
                if t != inner {
                    return ty_err(a.span, &format!("expected `{}`, found `{}`", self.types.show(inner), self.types.show(t)));
                }
                Ok(self.borrow_op(fb, p, true, pt, a.span))
            }
            TyKind::Ref(inner) => {
                let v = self.expr(fb, a, Some(inner))?;
                let v = self.coerce(fb, v, inner, a.span)?;
                let (p, _) = self.as_place(fb, v, a.span);
                Ok(self.borrow_op(fb, p, false, pt, a.span))
            }
            _ => {
                let v = self.expr(fb, a, Some(pt))?;
                let v = self.coerce(fb, v, pt, a.span)?;
                self.operand(fb, v, a.span)
            }
        }
    }

    pub fn borrow_op(&mut self, fb: &mut Fb, p: Place, mutable: bool, rt: TyId, span: Span) -> Operand {
        // Borrowing through a borrow local hands on the same reference.
        if p.proj.len() == 1 && p.proj[0] == Proj::Deref && fb.ty_of(p.local) == rt && !mutable {
            return Operand::Copy(Place::local(p.local));
        }
        let t = fb.temp(rt, span);
        fb.assign(Place::local(t), if mutable { Rvalue::RefMut(p) } else { Rvalue::Ref(p) }, span);
        if mutable {
            Operand::Move(Place::local(t))
        } else {
            Operand::Copy(Place::local(t))
        }
    }

    pub fn emit_call(&mut self, fb: &mut Fb, callee: Callee, args: Vec<Operand>, ret: TyId, span: Span) -> R<Val> {
        let callee_kind = match &callee {
            Callee::Fn(f) => Some(*f),
            _ => None,
        };
        let dest = fb.temp(ret, span);
        let next = fb.new_block();
        fb.term(Term::Call { callee, args, dest: Place::local(dest), next, span });
        fb.switch_to(next);
        if ret == types::NEVER {
            fb.term(Term::Unreachable);
            return Ok(Val::never());
        }
        // A function declared `-> ref T` or `-> inout T` returns a place; one
        // whose type parameter is a borrow (`mem.replace` of a `ref T`)
        // returns that borrow as a value.
        let projection = match &callee_kind {
            Some(f) => self.out[*f as usize].returns_ref,
            None => true,
        };
        if let TyKind::Ref(inner) | TyKind::RefMut(inner) = self.types.kind(ret).clone() {
            if projection {
                return Ok(Val::place(Place::deref(dest), inner));
            }
        }
        Ok(Val { vk: VK::Place(Place::local(dest)), ty: ret, temp: true })
    }

    fn call_comptime_closure(&mut self, fb: &mut Fb, l: Local, lf: FnId, args: &[ast::Expr], span: Span) -> R<Val> {
        let sig = self.out[lf as usize].sig.clone();
        if sig.params.len() != args.len() + 1 {
            return ty_err(span, &format!("this closure takes {} argument(s), {} given", sig.params.len() - 1, args.len()));
        }
        let envt = sig.params[0];
        let mut ops = Vec::new();
        let raw = self.types.ptr(types::U8);
        let e = fb.temp(raw, span);
        fb.assign(Place::local(e), Rvalue::Use(Operand::Copy(Place::local(l).with(Proj::Field(1)))), span);
        let ec = fb.temp(envt, span);
        fb.assign(Place::local(ec), Rvalue::Cast(Operand::Copy(Place::local(e)), envt, CastKind::Ptr), span);
        ops.push(Operand::Copy(Place::local(ec)));
        for (a, &pt) in args.iter().zip(&sig.params[1..]) {
            ops.push(self.arg_for_local_ty(fb, a, pt)?);
        }
        self.emit_call(fb, Callee::Fn(lf), ops, sig.ret, span)
    }

    /// A method call `recv.name(args)`.
    pub fn method_call(&mut self, fb: &mut Fb, recv: Val, name: &str, args: &[ast::Expr], span: Span, exp: Option<TyId>, _stmt: bool) -> R<Val> {
        let mut recv = recv;
        for _ in 0..8 {
            if let TyKind::Ptr(_) = self.types.kind(recv.ty) {
                recv = self.auto_deref(fb, recv, span)?;
            }
            if let Some((fid, iargs)) = self.find_method(recv.ty, name)? {
                return self.call_decl(fb, fid, iargs, Some(recv), args, span, exp);
            }
            if name != "deref" && self.find_method(recv.ty, "deref")?.is_some() {
                recv = self.method_call_val(fb, recv, "deref", vec![], span, None)?;
                continue;
            }
            break;
        }
        ty_err(span, &format!("`{}` has no method `{}`", self.types.show(recv.ty), name))
    }

    /// A method call whose arguments are already values.
    pub fn method_call_val(&mut self, fb: &mut Fb, recv: Val, name: &str, args: Vec<Val>, span: Span, exp: Option<TyId>) -> R<Val> {
        let Some((fid, iargs)) = self.find_method(recv.ty, name)? else {
            return ty_err(span, &format!("`{}` has no method `{}`", self.types.show(recv.ty), name));
        };
        self.call_decl_vals(fb, fid, iargs, Some(recv), args, span, exp)
    }

    pub fn call_static(&mut self, fb: &mut Fb, t: TyId, name: &str, args: Vec<Val>, span: Span) -> R<Val> {
        let Some((fid, iargs)) = self.find_method(t, name)? else {
            return ty_err(span, &format!("`{}` has no function `{}`", self.types.show(t), name));
        };
        self.call_decl_vals(fb, fid, iargs, None, args, span, None)
    }

    /// A call of a declared function: infers its compile-time arguments,
    /// makes the instance, and passes each argument as its parameter
    /// says.
    pub fn call_decl(&mut self, fb: &mut Fb, fid: u32, iargs: Vec<CVal>, recv: Option<Val>, args: &[ast::Expr], span: Span, exp: Option<TyId>) -> R<Val> {
        self.call_decl_inner(fb, fid, iargs, recv, Args::Ast(args), span, exp)
    }

    pub fn call_decl_vals(&mut self, fb: &mut Fb, fid: u32, iargs: Vec<CVal>, recv: Option<Val>, args: Vec<Val>, span: Span, exp: Option<TyId>) -> R<Val> {
        self.call_decl_inner(fb, fid, iargs, recv, Args::Vals(args), span, exp)
    }

    fn call_decl_inner(&mut self, fb: &mut Fb, fid: u32, iargs: Vec<CVal>, recv: Option<Val>, args: Args, span: Span, exp: Option<TyId>) -> R<Val> {
        let info = &self.fns[fid as usize];
        let decl = info.decl;
        let module = info.module;
        if !info.public && !self.same_package(module, fb.env.module) && !self.same_owner_module(fid, fb.env.module) {
            return ty_err(span, &format!("`{}` is private", decl.name));
        }
        if decl.is_unsafe && fb.unsafe_depth == 0 {
            return ty_err(span, &format!("`{}` is an unsafe function; call it in `unsafe` code", decl.name));
        }
        if decl.kind == ast::FnKind::Extern && fb.unsafe_depth == 0 {
            return ty_err(span, &format!("`{}` is a C function; call it in `unsafe` code", decl.name));
        }
        let params: Vec<&ast::Param> = decl.params.iter().collect();
        let has_self = params.first().map(|p| p.name == "self").unwrap_or(false);
        // Which parameters the given arguments fill.
        let nargs = match &args {
            Args::Ast(a) => a.len(),
            Args::Vals(v) => v.len(),
        } + recv.is_some() as usize;
        if recv.is_some() && !has_self {
            return ty_err(span, &format!("`{}` is not a method (it has no `self`); call it as `Type.{}(...)`", decl.name, decl.name));
        }
        let ncomptime = params.iter().filter(|p| p.mode == Mode::Comptime && !self.is_closure_param(p)).count();
        let nct_all = params.iter().filter(|p| p.mode == Mode::Comptime).count();
        let explicit_ct = nargs == params.len() && ncomptime > 0;
        let extra_args: Vec<ast::Expr> = match &args {
            Args::Ast(a) if decl.variadic && nargs > params.len() => a[params.len() - recv.is_some() as usize..].to_vec(),
            _ => Vec::new(),
        };
        let args = match args {
            Args::Ast(a) if !extra_args.is_empty() => Args::Ast(&a[..a.len() - extra_args.len()]),
            a => a,
        };
        let nargs = nargs - extra_args.len();
        if nargs != params.len() && nargs != params.len() - ncomptime {
            let want = params.len() - ncomptime - recv.is_some() as usize;
            return ty_err(span, &format!("`{}` takes {} argument(s), {} given", decl.name, want, nargs - recv.is_some() as usize));
        }
        // A function of a generic type named without its arguments
        // (`Vec.new()`, `Box.new(x)`): the impl's parameters are inferred
        // with the function's own.
        let owner = self.fns[fid as usize].owner;
        let impl_params: Vec<ast::Param> = match owner {
            Owner::Impl(imp) if iargs.is_empty() => self.impls[imp as usize].decl.params.clone(),
            _ => Vec::new(),
        };
        let nimpl = impl_params.len();
        let impl_self: Option<ast::Ty> = match owner {
            Owner::Impl(imp) if nimpl > 0 => Some(self.impls[imp as usize].decl.self_ty.clone()),
            _ => None,
        };
        let mut env = if nimpl > 0 {
            Env { module, names: Vec::new(), self_ty: None }
        } else {
            let (mut env, _) = self.fn_env(fid, &iargs);
            self.fn_self_ty(fid, &mut env)?;
            env
        };
        let mut cargs: Vec<Option<CVal>> = vec![None; nimpl + nct_all];
        let mut ct_names: Vec<String> = impl_params.iter().map(|p| p.name.clone()).collect();
        ct_names.extend(params.iter().filter(|p| p.mode == Mode::Comptime).map(|p| p.name.clone()));
        let mut ct_params: Vec<ast::Param> = impl_params.clone();
        ct_params.extend(params.iter().filter(|q| q.mode == Mode::Comptime).map(|q| (*q).clone()));
        // The expected result can decide the impl's parameters first.
        if nimpl > 0 {
            if let (Some(e), Some(rt)) = (exp, decl.ret.as_ref()) {
                let pat = match &rt.kind {
                    ast::TyKind::Path(p, None) if p.len() == 1 && p[0] == "Self" => impl_self.clone().unwrap(),
                    _ => rt.clone(),
                };
                let mut binds = cargs.clone();
                if self.match_ty_env(&pat, e, &ct_params, &env, &mut binds)? {
                    cargs = binds;
                }
            }
        }
        // Lower the runtime arguments, in order, binding compile-time
        // parameters as their types are seen.
        let mut vals: Vec<Option<(Val, Span)>> = Vec::new();
        let mut ast_args: Vec<Option<&ast::Expr>> = Vec::new();
        let mut val_args: Vec<Val> = Vec::new();
        match args {
            Args::Ast(a) => ast_args = a.iter().map(Some).collect(),
            Args::Vals(v) => val_args = v,
        }
        let mut ai = 0usize;
        let mut vi = 0usize;
        let mut ci = nimpl;
        let mut recv = recv;
        for p in &params {
            if p.mode == Mode::Comptime && self.is_closure_param(p) {
                // A closure for a compile-time closure parameter: one instance
                // per closure.
                let Some(a) = ast_args.get(ai).copied().flatten() else { return ty_err(span, "a closure argument is missing") };
                ai += 1;
                let known = self.partial_env_self(&env, &ct_names, &cargs, nimpl, impl_self.as_ref());
                let pty = self.resolve_ty(p.ty.as_ref().unwrap(), &known).ok();
                let cv = match &a.kind {
                    E::Name(n) if self.comptime_closures.iter().any(|c| c.0 == fb.id && &c.1 == n) => {
                        let c = self.comptime_closures.iter().find(|c| c.0 == fb.id && &c.1 == n).cloned().unwrap();
                        let lt = fb.ty_of(c.2);
                        let envt = self.out[c.3 as usize].sig.params[0];
                        vals.push(Some((Val::place(Place::local(c.2), lt), a.span)));
                        CVal::Lambda(c.3, envt)
                    }
                    E::Lambda(..) => {
                        self.last_lambda = None;
                        let v = self.expr(fb, a, pty)?;
                        let Some((lf, envt)) = self.last_lambda.take() else { return ty_err(a.span, "expected a closure") };
                        vals.push(Some((v, a.span)));
                        CVal::Lambda(lf, envt)
                    }
                    _ => return ty_err(a.span, "a compile-time closure parameter takes a closure written here (`fn(x) { ... }`)"),
                };
                env.names.push((p.name.clone(), cv.clone()));
                cargs[ci] = Some(cv);
                ci += 1;
                continue;
            }
            if p.mode == Mode::Comptime {
                if explicit_ct {
                    let Some(a) = ast_args.get(ai).copied().flatten() else { return ty_err(span, "compile-time arguments must be written") };
                    ai += 1;
                    let cv = self.comptime_call_arg(fb, p, module, a, &env)?;
                    env.names.push((p.name.clone(), cv.clone()));
                    cargs[ci] = Some(cv);
                }
                ci += 1;
                vals.push(None);
                continue;
            }
            if p.name == "self" && recv.is_some() {
                let r = recv.take().unwrap();
                vals.push(Some((r, span)));
                continue;
            }
            // The parameter's type, if the compile-time arguments so far
            // decide it.
            let known = self.partial_env_self(&env, &ct_names, &cargs, nimpl, impl_self.as_ref());
            let pty = match &p.ty {
                Some(t) => self.resolve_ty(t, &known).ok(),
                None => known.self_ty,
            };
            let v = if let Some(a) = ast_args.get(ai).copied().flatten() {
                ai += 1;
                let sp = a.span;
                // A closure for a compile-time closure parameter.
                if p.mode == Mode::Inout {
                    let (pl, t) = self.mut_place(fb, a)?;
                    (Val::place(pl, t), sp)
                } else {
                    let v = self.expr(fb, a, pty)?;
                    let lent_str = p.mode == Mode::Let && v.ty == types::STR && pty.is_some() && pty == self.string_ty();
                    let v = match pty {
                        Some(t) if !lent_str => self.coerce(fb, v, t, sp)?,
                        _ => v,
                    };
                    (v, sp)
                }
            } else {
                let v = val_args[vi].clone();
                vi += 1;
                let v = match pty {
                    Some(t) => self.coerce(fb, v, t, span)?,
                    None => v,
                };
                (v, span)
            };
            if pty.is_none() {
                if let Some(t) = &p.ty {
                    let mut binds: Vec<Option<CVal>> = cargs.clone();
                    let pat = match &t.kind {
                        ast::TyKind::Path(p, None) if p.len() == 1 && p[0] == "Self" && impl_self.is_some() => impl_self.clone().unwrap(),
                        _ => t.clone(),
                    };
                    if !self.match_ty_env(&pat, v.0.ty, &ct_params, &env, &mut binds)? {
                        return ty_err(v.1, &format!("this argument has type `{}`, which does not fit the parameter's type", self.types.show(v.0.ty)));
                    }
                    cargs = binds;
                }
            }
            vals.push(Some(v));
        }
        // Compile-time closure parameters take the closures given.
        for (i, p) in impl_params.iter().enumerate() {
            if cargs[i].is_none() {
                return ty_err(span, &format!("cannot infer `{}` of `{}`; write the type's arguments", p.name, decl.name));
            }
        }
        let mut ci = nimpl;
        for (pi, p) in params.iter().enumerate() {
            if p.mode != Mode::Comptime {
                continue;
            }
            if cargs[ci].is_none() {
                // Not inferable: maybe from the expected result type.
                if let (Some(rt), Some(e)) = (&decl.ret, exp) {
                    let mut binds = cargs.clone();
                    if self.match_ty_env(rt, e, &ct_params, &env, &mut binds)? {
                        cargs = binds;
                    }
                }
            }
            if cargs[ci].is_none() {
                return ty_err(span, &format!("cannot infer the compile-time argument `{}` of `{}`; pass it explicitly", p.name, decl.name));
            }
            let _ = pi;
            ci += 1;
        }
        let mut all = iargs.clone();
        if nimpl > 0 {
            let Owner::Impl(imp) = owner else { unreachable!() };
            let ia: Vec<CVal> = cargs[..nimpl].iter().map(|c| c.clone().unwrap()).collect();
            let imodule = self.impls[imp as usize].module;
            for (p, a) in impl_params.iter().zip(&ia) {
                if let CVal::Type(t) = a {
                    for bnd in self.param_bounds(p, imodule)? {
                        if !self.implements(bnd, *t)? {
                            return ty_err(span, &format!("`{}` does not implement `{}`", self.types.show(*t), self.traits[bnd as usize].name));
                        }
                    }
                }
            }
            all = ia;
        }
        if matches!(self.fns[fid as usize].owner, Owner::Trait(_)) && all.is_empty() {
            all.push(CVal::Type(env.self_ty.unwrap()));
        }
        // Bounds.
        let mut ci = nimpl;
        for p in &params {
            if p.mode != Mode::Comptime {
                continue;
            }
            let cv = cargs[ci].clone().unwrap();
            if let CVal::Type(t) = cv {
                for b in self.param_bounds(p, module)? {
                    if !self.implements(b, t)? {
                        return ty_err(span, &format!("`{}` does not implement `{}`, which `{}` requires of `{}`", self.types.show(t), self.traits[b as usize].name, decl.name, p.name));
                    }
                }
            }
            all.push(cv);
            ci += 1;
        }
        let id = self.instance(fid, all, span)?;
        let fsig = self.out[id as usize].sig.clone();
        let pass = self.out[id as usize].pass.clone();
        // Pass each argument.
        let mut ops = Vec::new();
        let mut li = 0;
        for (p, v) in params.iter().zip(vals) {
            if p.mode == Mode::Comptime {
                if let Some(CVal::Lambda(..)) = self.inst_env_get(id, &p.name) {
                    let (v, sp) = v.unwrap();
                    let o = self.operand(fb, v, sp)?;
                    ops.push(o);
                    li += 1;
                }
                continue;
            }
            let (v, sp) = v.unwrap();
            let lt = fsig.params[li];
            // Now that the parameter's type is known, convert to it.
            let v = if p.mode == Mode::Inout {
                v
            } else {
                let vt = if pass[li] == ParamPass::Borrow { self.types.pointee(lt).unwrap() } else { lt };
                // A `str` lent where a `String` is borrowed: a `String`
                // over the same bytes, without copying (`map.get("key")`).
                if pass[li] == ParamPass::Borrow && v.ty == types::STR && Some(vt) == self.string_ty() {
                    self.call_static(fb, vt, "from_static", vec![v], sp)?
                } else {
                    self.coerce(fb, v, vt, sp)?
                }
            };
            let op = match (p.mode, pass[li]) {
                (Mode::Inout, _) => {
                    let VK::Place(pl) = v.vk else { return ty_err(sp, "expected a place") };
                    if !self.place_mutable(fb, &pl) {
                        return ty_err(sp, &self.not_mutable_msg(fb, &pl));
                    }
                    if v.temp && p.name != "self" {
                        return ty_err(sp, "an `inout` argument must be a place, not a temporary value");
                    }
                    self.borrow_op(fb, pl, true, lt, sp)
                }
                (_, ParamPass::Borrow) => {
                    let (pl, _) = self.as_place(fb, v, sp);
                    self.borrow_op(fb, pl, false, lt, sp)
                }
                (Mode::Let, _) => {
                    // By value: plain.
                    match v.vk.clone() {
                        VK::Place(pl) if !self.types.is_plain(v.ty) => {
                            // A view of a non-plain place: copy the bits.
                            Operand::Copy(pl)
                        }
                        _ => self.operand(fb, v, sp)?,
                    }
                }
                _ => self.operand(fb, v, sp)?,
            };
            ops.push(op);
            li += 1;
        }
        // The variable arguments of a C function, with C's promotions.
        for a in &extra_args {
            let v = self.expr(fb, a, None)?;
            let pu8 = self.types_ptr_u8();
            let v = if v.ty == types::STR { self.coerce(fb, v, pu8, a.span)? } else { v };
            let t = v.ty;
            let o = self.operand(fb, v, a.span)?;
            let o = match self.types.kind(t).clone() {
                TyKind::Int(i) if i.bits < 32 => {
                    let to = if i.signed { types::I32 } else { types::U32 };
                    let c = self.rvalue(fb, Rvalue::Cast(o, to, CastKind::Numeric), to, a.span);
                    Operand::Copy(self.place_of_val(c))
                }
                TyKind::Float(32) => {
                    let c = self.rvalue(fb, Rvalue::Cast(o, types::F64, CastKind::Numeric), types::F64, a.span);
                    Operand::Copy(self.place_of_val(c))
                }
                TyKind::Bool => {
                    let c = self.rvalue(fb, Rvalue::Cast(o, types::I32, CastKind::Numeric), types::I32, a.span);
                    Operand::Copy(self.place_of_val(c))
                }
                k if self.types.is_scalar(t) || matches!(k, TyKind::Int(_) | TyKind::Float(_)) => o,
                _ => return ty_err(a.span, "only numbers and pointers can be passed to a C function's `...`"),
            };
            ops.push(o);
        }
        self.emit_call(fb, Callee::Fn(id), ops, fsig.ret, span)
    }

    fn inst_env_get(&self, id: FnId, name: &str) -> Option<CVal> {
        self.inst_info.get(id as usize)?.as_ref()?.env.get(name).cloned()
    }

    fn same_owner_module(&self, fid: u32, module: u32) -> bool {
        // Impl functions are visible where the type is.
        match self.fns[fid as usize].owner {
            Owner::Impl(i) => self.impls[i as usize].module == module,
            _ => false,
        }
    }

    fn comptime_call_arg(&mut self, fb: &mut Fb, p: &ast::Param, module: u32, a: &ast::Expr, env: &Env) -> R<CVal> {
        let _ = env;
        let fenv = fb.env.clone();
        self.comptime_arg(p, module, a, &fenv)
    }

    fn partial_env_self(&mut self, env: &Env, names: &[String], vals: &[Option<CVal>], nimpl: usize, impl_self: Option<&ast::Ty>) -> Env {
        let mut e = self.partial_env(env, names, vals);
        if nimpl > 0 && e.self_ty.is_none() && vals[..nimpl].iter().all(|v| v.is_some()) {
            if let Some(t) = impl_self {
                if let Ok(st) = self.resolve_ty(t, &e) {
                    e.self_ty = Some(st);
                }
            }
        }
        e
    }

    fn partial_env(&self, env: &Env, names: &[String], vals: &[Option<CVal>]) -> Env {
        let mut e = env.clone();
        for (n, v) in names.iter().zip(vals) {
            if let Some(v) = v {
                e.names.push((n.clone(), v.clone()));
            }
        }
        e
    }

    /// Matches a parameter type against an argument's type, binding the
    /// compile-time parameters it mentions.
    fn match_ty_env(&mut self, pat: &ast::Ty, t: TyId, params: &[ast::Param], env: &Env, binds: &mut Vec<Option<CVal>>) -> R<bool> {
        use ast::TyKind as A;
        let k = self.types.kind(t).clone();
        match (&pat.kind, &k) {
            (A::Path(p, None), _) if p.len() == 1 && params.iter().any(|q| q.name == p[0]) => {
                let i = params.iter().position(|q| q.name == p[0]).unwrap();
                let v = CVal::Type(t);
                match &binds[i] {
                    Some(old) => Ok(*old == v),
                    None => {
                        binds[i] = Some(v);
                        Ok(true)
                    }
                }
            }
            (A::Ptr(inner), TyKind::Ptr(x)) => self.match_ty_env(inner, *x, params, env, binds),
            (A::Ref(inner, false), TyKind::Ref(x)) | (A::Ref(inner, true), TyKind::RefMut(x)) => self.match_ty_env(inner, *x, params, env, binds),
            (A::Slice(inner), TyKind::Slice(x)) => self.match_ty_env(inner, *x, params, env, binds),
            // What coerces to a slice: arrays, and types with `as_slice`.
            (A::Slice(inner), TyKind::Array(x, _)) => self.match_ty_env(inner, *x, params, env, binds),
            (A::Slice(inner), TyKind::Adt(_)) => {
                let Some((fid, iargs)) = self.find_method(t, "as_slice")? else { return Ok(false) };
                let id = self.instance(fid, iargs, pat.span)?;
                let r = self.out[id as usize].sig.ret;
                match self.types.kind(r).clone() {
                    TyKind::Slice(x) => self.match_ty_env(inner, x, params, env, binds),
                    _ => Ok(false),
                }
            }
            (A::Array(inner, n), TyKind::Array(x, len)) => {
                if !self.match_ty_env(inner, *x, params, env, binds)? {
                    return Ok(false);
                }
                if let ast::ExprKind::Name(nm) = &n.kind {
                    if let Some(i) = params.iter().position(|q| &q.name == nm) {
                        let v = CVal::Int(*len as i128);
                        return Ok(match &binds[i] {
                            Some(old) => *old == v,
                            None => {
                                binds[i] = Some(v);
                                true
                            }
                        });
                    }
                }
                Ok(true)
            }
            (A::Tuple(ps), TyKind::Tuple(xs)) => {
                if ps.len() != xs.len() {
                    return Ok(false);
                }
                for (p, x) in ps.iter().zip(xs.clone()) {
                    if !self.match_ty_env(p, x, params, env, binds)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (A::Fn(ps, r), TyKind::Closure(sig)) | (A::FnPtr(ps, r), TyKind::FnPtr(sig)) => {
                if ps.len() != sig.params.len() {
                    return Ok(false);
                }
                for ((m, p), &x) in ps.iter().zip(&sig.params) {
                    let x = if *m != Mode::Sink && self.types.is_ref(x) { self.types.pointee(x).unwrap() } else { x };
                    if !self.match_ty_env(p, x, params, env, binds)? {
                        return Ok(false);
                    }
                }
                match r {
                    Some(r) => self.match_ty_env(r, sig.ret, params, env, binds),
                    None => Ok(sig.ret == types::UNIT),
                }
            }
            (A::Path(p, Some(args)), TyKind::Adt(i)) => {
                let decl = self.types.adts[*i as usize].decl;
                match self.lookup_path(env.module, p) {
                    Some((Sym::Adt(d), _)) if d == decl => {}
                    _ => return Ok(false),
                }
                let concrete: Vec<CVal> = self.adt_args(t);
                if args.len() != concrete.len() {
                    return Ok(false);
                }
                for (a, c) in args.iter().zip(concrete) {
                    match c {
                        CVal::Type(ct) => {
                            let Some(at) = super::expr_as_ty(a) else { return Ok(false) };
                            if !self.match_ty_env(&at, ct, params, env, binds)? {
                                return Ok(false);
                            }
                        }
                        v => {
                            if let ast::ExprKind::Name(nm) = &a.kind {
                                if let Some(i) = params.iter().position(|q| &q.name == nm) {
                                    match &binds[i] {
                                        Some(old) if *old != v => return Ok(false),
                                        _ => binds[i] = Some(v),
                                    }
                                }
                            }
                        }
                    }
                }
                Ok(true)
            }
            _ => {
                // No unknown inside: resolve it and compare.
                let known = {
                    let mut e = env.clone();
                    for (q, b) in params.iter().zip(binds.iter()) {
                        if let Some(b) = b {
                            e.names.push((q.name.clone(), b.clone()));
                        }
                    }
                    e
                };
                match self.resolve_ty(pat, &known) {
                    Ok(pt) => Ok(pt == t || self.coercible(t, pt)),
                    Err(_) => Ok(false),
                }
            }
        }
    }

    fn coercible(&mut self, from: TyId, to: TyId) -> bool {
        if from == types::NEVER {
            return true;
        }
        if Some(to) == self.string_ty() && from == types::STR {
            return true;
        }
        matches!((self.types.kind(from), self.types.kind(to)), (TyKind::Array(a, _), TyKind::Slice(b)) if a == b)
    }

    pub fn adt_args(&self, t: TyId) -> Vec<CVal> {
        self.adt_args_of.get(&t).cloned().unwrap_or_default()
    }

    /// Whether a method of this name takes `inout self` (in any impl).
    pub fn method_name_inout(&self, name: &str) -> bool {
        self.fns.iter().any(|f| f.decl.name == name && f.owner != Owner::Free && f.decl.params.first().map(|p| p.name == "self" && p.mode == Mode::Inout).unwrap_or(false))
    }

    pub fn is_closure_param(&self, p: &ast::Param) -> bool {
        matches!(&p.ty, Some(ast::Ty { kind: ast::TyKind::Fn(..), .. }))
    }

    // ---- loops ----

    fn for_expr(&mut self, fb: &mut Fb, index: Option<&(String, Span)>, pat: &ast::Pat, it: &ast::Expr, body: &ast::Block, span: Span) -> R<Val> {
        fb.push_scope(false);
        // `for i in a..b`
        if let E::Range(lo, hi) = &it.kind {
            let (Some(lo), Some(hi)) = (lo, hi) else { return ty_err(it.span, "a `for` range needs both ends") };
            let lv = self.expr(fb, lo, None)?;
            let hv = self.expr(fb, hi, Some(lv.ty))?;
            let t = lv.ty;
            let lv = if matches!(lo.kind, E::Int(_)) && hv.ty != t { self.expr(fb, lo, Some(hv.ty))? } else { lv };
            let t = lv.ty;
            if !self.types.is_int(t) || hv.ty != t {
                return ty_err(it.span, &format!("a range needs two integers of the same type, found `{}` and `{}`", self.types.show(t), self.types.show(hv.ty)));
            }
            let lo_o = self.operand(fb, lv, lo.span)?;
            let hi_o = self.operand(fb, hv, hi.span)?;
            let i = fb.new_local(t, None, true, LocalKind::Temp, span);
            fb.push(Stmt::StorageLive(i));
            fb.scopes.last_mut().unwrap().locals.push(i);
            let end = fb.new_local(t, None, false, LocalKind::Temp, span);
            fb.push(Stmt::StorageLive(end));
            fb.scopes.last_mut().unwrap().locals.push(end);
            fb.assign(Place::local(i), Rvalue::Use(lo_o), span);
            fb.assign(Place::local(end), Rvalue::Use(hi_o), span);
            let head = fb.new_block();
            let step = fb.new_block();
            let exit = fb.new_block();
            fb.goto(head);
            let c = fb.temp(types::BOOL, span);
            fb.assign(Place::local(c), Rvalue::Bin(Op::Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(end))), span);
            let bb = fb.new_block();
            fb.term(Term::Switch { discr: Operand::Copy(Place::local(c)), targets: vec![(0, exit)], otherwise: bb });
            fb.switch_to(bb);
            fb.push_scope(false);
            match &pat.kind {
                ast::PatKind::Name(n, _) => {
                    let x = fb.declare(n, t, false, VarKind::Owned, pat.span);
                    fb.assign(Place::local(x), Rvalue::Use(Operand::Copy(Place::local(i))), span);
                }
                ast::PatKind::Wild => {}
                _ => return ty_err(pat.span, "a range loop binds one name"),
            }
            if index.is_some() {
                return ty_err(span, "a range loop has no separate index");
            }
            fb.loops.push(LoopCtx { brk: exit, cont: step, depth: fb.depth() - 1 });
            self.block(fb, body, Some(types::UNIT), false)?;
            fb.loops.pop();
            self.pop_scope(fb);
            fb.goto(step);
            fb.assign(Place::local(i), Rvalue::Bin(Op::AddWrap, Operand::Copy(Place::local(i)), Operand::Const(Const::Int(1, t))), span);
            fb.goto(head);
            fb.switch_to(exit);
            self.pop_scope(fb);
            return Ok(Val::unit());
        }
        let v = self.expr(fb, it, None)?;
        // A borrow held as a value (a `ref Vec(T)` field): what it points to.
        let v = if self.types.is_ref(v.ty) { self.auto_deref(fb, v, it.span)? } else { v };
        // Arrays, slices and strings: by index.
        let vt = v.ty;
        let mut v = v;
        if let TyKind::Array(..) = self.types.kind(vt) {
            let TyKind::Array(e, _) = self.types.kind(vt).clone() else { unreachable!() };
            let st = self.view_ty(TyKind::Slice(e));
            v = self.coerce(fb, v, st, it.span)?;
        }
        if let TyKind::Slice(_) | TyKind::Str = self.types.kind(v.ty) {
            let r = self.for_view(fb, index, pat, v, body, span);
            self.pop_scope(fb);
            return r;
        }
        if self.types.adt_of(v.ty).is_none() {
            return ty_err(it.span, &format!("cannot loop over `{}`", self.types.show(v.ty)));
        }
        // An iterator (`next`), or something with `iter()`.
        let iter_v = if self.find_method(v.ty, "next")?.is_some() {
            v
        } else if self.find_method(v.ty, "iter")?.is_some() {
            self.method_call_val(fb, v, "iter", vec![], it.span, None)?
        } else if self.find_method(v.ty, "as_slice")?.is_some() || self.find_method(v.ty, "as_str")?.is_some() {
            let name = if self.find_method(v.ty, "as_slice")?.is_some() { "as_slice" } else { "as_str" };
            let s = self.method_call_val(fb, v, name, vec![], it.span, None)?;
            let r = self.for_view(fb, index, pat, s, body, span);
            self.pop_scope(fb);
            return r;
        } else {
            return ty_err(it.span, &format!("cannot loop over `{}`: it has no `next` or `iter` method", self.types.show(v.ty)));
        };
        let it_t = iter_v.ty;
        let o = self.operand(fb, iter_v, it.span)?;
        let itl = fb.new_local(it_t, None, true, LocalKind::Temp, span);
        fb.push(Stmt::StorageLive(itl));
        fb.scopes.last_mut().unwrap().locals.push(itl);
        fb.assign(Place::local(itl), Rvalue::Use(o), span);
        let idx = if index.is_some() {
            let l = fb.new_local(types::I64, None, true, LocalKind::Temp, span);
            fb.push(Stmt::StorageLive(l));
            fb.scopes.last_mut().unwrap().locals.push(l);
            fb.assign(Place::local(l), Rvalue::Use(Operand::Const(Const::Int(0, types::I64))), span);
            Some(l)
        } else {
            None
        };
        let head = fb.new_block();
        let step = fb.new_block();
        let exit = fb.new_block();
        fb.goto(head);
        fb.push_scope(true);
        let nv = self.method_call_val(fb, Val::place(Place::local(itl), it_t), "next", vec![], it.span, None)?;
        let nt = nv.ty;
        let ok = self.types.adt_of(nt).map(|a| Some(a.decl) == self.lang.option).unwrap_or(false);
        if !ok {
            return ty_err(it.span, &format!("`next` must return an `Option`, found `{}`", self.types.show(nt)));
        }
        let o = self.operand(fb, nv, it.span)?;
        let cur = fb.new_local(nt, None, true, LocalKind::Temp, span);
        fb.push(Stmt::StorageLive(cur));
        fb.assign(Place::local(cur), Rvalue::Use(o), span);
        let vs = self.types.variants(nt).unwrap().clone();
        let some = vs.iter().position(|v| v.name == "Some").unwrap() as u32;
        self.pop_scope(fb);
        let d = fb.new_local(types::I64, None, true, LocalKind::Temp, span);
        fb.assign(Place::local(d), Rvalue::Discriminant(Place::local(cur)), span);
        let bb = fb.new_block();
        let none_b = fb.new_block();
        fb.term(Term::Switch { discr: Operand::Copy(Place::local(d)), targets: vec![(some as i128, bb)], otherwise: none_b });
        fb.switch_to(none_b);
        fb.push(Stmt::Forget(cur));
        fb.push(Stmt::StorageDead(cur));
        fb.goto(exit);
        fb.switch_to(bb);
        fb.push_scope(false);
        let et = vs[some as usize].fields[0];
        let item = Val { vk: VK::Op(Operand::Move(Place::local(cur).with(Proj::Variant(some)).with(Proj::Field(0)))), ty: et, temp: false };
        if let Some((n, sp)) = index {
            let il = fb.declare(n, types::I64, false, VarKind::Owned, *sp);
            fb.assign(Place::local(il), Rvalue::Use(Operand::Copy(Place::local(idx.unwrap()))), span);
        }
        self.destructure(fb, pat, item, super::pat::BindMode::Owned, span)?;
        fb.push(Stmt::Forget(cur));
        fb.push(Stmt::StorageDead(cur));
        fb.loops.push(LoopCtx { brk: exit, cont: step, depth: fb.depth() - 1 });
        self.block(fb, body, Some(types::UNIT), false)?;
        fb.loops.pop();
        self.pop_scope(fb);
        fb.goto(step);
        if let Some(l) = idx {
            fb.assign(Place::local(l), Rvalue::Bin(Op::AddWrap, Operand::Copy(Place::local(l)), Operand::Const(Const::Int(1, types::I64))), span);
        }
        fb.goto(head);
        fb.switch_to(exit);
        self.pop_scope(fb);
        Ok(Val::unit())
    }

    /// A loop over a slice or `str`, by index; elements are borrowed (or
    /// copied, if plain).
    fn for_view(&mut self, fb: &mut Fb, index: Option<&(String, Span)>, pat: &ast::Pat, v: Val, body: &ast::Block, span: Span) -> R<Val> {
        let vt = v.ty;
        let et = match self.types.kind(vt) {
            TyKind::Slice(e) => *e,
            _ => types::U8,
        };
        let o = self.operand(fb, v, span)?;
        let view = fb.new_local(vt, None, false, LocalKind::Temp, span);
        fb.push(Stmt::StorageLive(view));
        fb.scopes.last_mut().unwrap().locals.push(view);
        fb.assign(Place::local(view), Rvalue::Use(o), span);
        let i = fb.new_local(types::I64, None, true, LocalKind::Temp, span);
        fb.push(Stmt::StorageLive(i));
        fb.scopes.last_mut().unwrap().locals.push(i);
        fb.assign(Place::local(i), Rvalue::Use(Operand::Const(Const::Int(0, types::I64))), span);
        let head = fb.new_block();
        let step = fb.new_block();
        let exit = fb.new_block();
        fb.goto(head);
        let c = fb.temp(types::BOOL, span);
        fb.assign(Place::local(c), Rvalue::Bin(Op::Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(view).with(Proj::Field(1)))), span);
        let bb = fb.new_block();
        fb.term(Term::Switch { discr: Operand::Copy(Place::local(c)), targets: vec![(0, exit)], otherwise: bb });
        fb.switch_to(bb);
        fb.push_scope(false);
        let pt = self.types.ptr(et);
        let a = fb.temp(pt, span);
        fb.assign(Place::local(a), Rvalue::Offset(Operand::Copy(Place::local(view).with(Proj::Field(0))), Operand::Copy(Place::local(i))), span);
        if let Some((n, sp)) = index {
            let il = fb.declare(n, types::I64, false, VarKind::Owned, *sp);
            fb.assign(Place::local(il), Rvalue::Use(Operand::Copy(Place::local(i))), span);
        }
        let elem = Val::place(Place::local(a).with(Proj::Deref), et);
        self.destructure(fb, pat, elem, super::pat::BindMode::Auto, span)?;
        fb.loops.push(LoopCtx { brk: exit, cont: step, depth: fb.depth() - 1 });
        self.block(fb, body, Some(types::UNIT), false)?;
        fb.loops.pop();
        self.pop_scope(fb);
        fb.goto(step);
        fb.assign(Place::local(i), Rvalue::Bin(Op::AddWrap, Operand::Copy(Place::local(i)), Operand::Const(Const::Int(1, types::I64))), span);
        fb.goto(head);
        fb.switch_to(exit);
        Ok(Val::unit())
    }

    // ---- closures ----

    fn lambda(&mut self, fb: &mut Fb, params: &[ast::LambdaParam], ret: Option<&ast::Ty>, body: &ast::Block, exp: Option<TyId>, span: Span) -> R<Val> {
        let env = fb.env.clone();
        let (exp_sig, want_ptr) = match exp.map(|t| self.types.kind(t).clone()) {
            Some(TyKind::Closure(s)) => (Some(s), false),
            Some(TyKind::FnPtr(s)) => (Some(s), true),
            _ => (None, false),
        };
        if let Some(s) = &exp_sig {
            if s.params.len() != params.len() {
                return ty_err(span, &format!("a closure with {} parameter(s) is expected", s.params.len()));
            }
        }
        // Parameter types: written, or the expected ones (already lowered:
        // borrows for non-plain values).
        let mut ptys = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let t = match (&p.ty, &exp_sig) {
                (Some(t), _) => {
                    let t = self.resolve_ty(t, &env)?;
                    self.param_local_ty(Mode::Let, t).0
                }
                (None, Some(s)) => s.params[i],
                (None, None) => return ty_err(p.span, "the type of this closure parameter must be written"),
            };
            ptys.push(t);
        }
        // Captures: names used inside that are variables outside.
        let mut used = Vec::new();
        collect_names_block(body, &mut used);
        let pnames: Vec<&str> = params.iter().map(|p| p.name.as_str()).collect();
        let mut caps: Vec<(String, Place, TyId, bool)> = Vec::new();
        for n in used {
            if pnames.contains(&n.as_str()) || caps.iter().any(|c| c.0 == n) {
                continue;
            }
            if let Some(v) = fb.lookup(&n) {
                let p = self.var_place(fb, v);
                let t = self.place_ty(fb, &p);
                let m = self.place_mutable(fb, &p);
                caps.push((n, p, t, m));
            }
        }
        if want_ptr && !caps.is_empty() {
            return ty_err(span, &format!("a `fnptr` cannot capture variables, and this closure uses `{}`", caps[0].0));
        }
        let mut env_fields = Vec::new();
        for c in &caps {
            env_fields.push(if c.3 { self.types.refmut(c.2) } else { self.types.refty(c.2) });
        }
        let env_t = self.types.tuple(env_fields.clone());
        let env_ref = self.types.refty(env_t);
        // The lifted function.
        let id = self.out.len() as FnId;
        let ret_t = match (ret, &exp_sig) {
            (Some(r), _) => Some(self.resolve_ty(r, &env)?),
            (None, Some(s)) => Some(s.ret),
            (None, None) => None,
        };
        let mut lparams = Vec::new();
        if !want_ptr {
            lparams.push(env_ref);
        }
        lparams.extend(ptys.iter().copied());
        let n = self.next_lambda();
        let fname = format!("{}.closure{}", self.out[fb.id as usize].name, n);
        self.out.push(Function {
            symbol: format!("closure.{}.{}", n, id),
            name: fname,
            sig: Sig { params: lparams.clone(), ret: ret_t.unwrap_or(types::UNIT) },
            pass: lparams.iter().map(|&t| if self.types.is_ref(t) { ParamPass::Borrow } else { ParamPass::Value }).collect(),
            body: None,
            linkage: Linkage::Internal,
            variadic: false,
            returns_ref: false,
            span,
        });
        self.inst_info.push(None);
        let mut lfb = Fb::new(id, env.clone(), ret_t.unwrap_or(types::UNIT), RetMode::Value, span);
        lfb.unsafe_depth = fb.unsafe_depth;
        if !want_ptr {
            let el = lfb.new_local(env_ref, Some("env".into()), false, LocalKind::Arg, span);
            lfb.env_local = Some(el);
            for (i, c) in caps.iter().enumerate() {
                lfb.bind_var(&c.0, Var { local: el, kind: VarKind::Capture(i as u32) });
            }
        }
        for (p, &t) in params.iter().zip(&ptys) {
            let kind = if self.types.is_ref(t) { VarKind::Borrow } else { VarKind::Owned };
            let l = lfb.new_local(t, Some(p.name.clone()), false, LocalKind::Arg, p.span);
            lfb.bind_var(&p.name, Var { local: l, kind });
        }
        lfb.body.arg_count = lparams.len();
        // The return type, if not known, is the body's.
        let rt = match ret_t {
            Some(t) => t,
            None => {
                lfb.push_scope(true);
                let probe = self.block(&mut lfb, body, None, true)?;
                let t = if probe.ty == types::NEVER { types::UNIT } else { probe.ty };
                // Lower again with the type known.
                lfb = Fb::new(id, env.clone(), t, RetMode::Value, span);
                lfb.unsafe_depth = fb.unsafe_depth;
                if !want_ptr {
                    let el = lfb.new_local(env_ref, Some("env".into()), false, LocalKind::Arg, span);
                    lfb.env_local = Some(el);
                    for (i, c) in caps.iter().enumerate() {
                        lfb.bind_var(&c.0, Var { local: el, kind: VarKind::Capture(i as u32) });
                    }
                }
                for (p, &pt) in params.iter().zip(&ptys) {
                    let kind = if self.types.is_ref(pt) { VarKind::Borrow } else { VarKind::Owned };
                    let l = lfb.new_local(pt, Some(p.name.clone()), false, LocalKind::Arg, p.span);
                    lfb.bind_var(&p.name, Var { local: l, kind });
                }
                lfb.body.arg_count = lparams.len();
                self.out[id as usize].sig.ret = t;
                t
            }
        };
        lfb.body.locals[0].ty = rt;
        self.lower_body(&mut lfb, body, rt)?;
        self.out[id as usize].body = Some(lfb.body);
        let sig = Sig { params: ptys, ret: rt };
        self.last_lambda = Some((id, env_ref));
        if want_ptr {
            let t = self.types.intern(TyKind::FnPtr(sig));
            return Ok(Val::op(Operand::Const(Const::Fn(id)), t));
        }
        // The environment lives as long as the block around the closure.
        let envl = fb.block_temp(env_t, span);
        let mut ops = Vec::new();
        for (c, &ft) in caps.iter().zip(&env_fields) {
            let r = fb.block_temp(ft, span);
            fb.assign(Place::local(r), if c.3 { Rvalue::RefMut(c.1.clone()) } else { Rvalue::Ref(c.1.clone()) }, span);
            ops.push(Operand::Move(Place::local(r)));
        }
        fb.assign(Place::local(envl), Rvalue::Aggregate(Agg::Struct(env_t), ops), span);
        let er = fb.block_temp(env_ref, span);
        fb.assign(Place::local(er), Rvalue::Ref(Place::local(envl)), span);
        let ct = self.types.intern(TyKind::Closure(sig));
        let v = self.rvalue(fb, Rvalue::Aggregate(Agg::Closure(ct), vec![Operand::Const(Const::Fn(id)), Operand::Copy(Place::local(er))]), ct, span);
        Ok(v)
    }
}

enum Args<'x> {
    Ast(&'x [ast::Expr]),
    Vals(Vec<Val>),
}

fn p_is_type_call(e: &ast::Expr) -> bool {
    matches!(&e.kind, E::Call(c, _) if expr_path(c).is_some())
}

/// Every name an expression mentions (for closure captures).
pub fn collect_names_block(b: &ast::Block, out: &mut Vec<String>) {
    for s in &b.stmts {
        match &s.kind {
            StmtKind::Let { value, .. } => collect_names(value, out),
            StmtKind::Assign(a, v) | StmtKind::OpAssign(_, a, v) => {
                collect_names(a, out);
                collect_names(v, out);
            }
            StmtKind::Expr(e) => collect_names(e, out),
        }
    }
    if let Some(t) = &b.tail {
        collect_names(t, out);
    }
}

pub fn collect_names(e: &ast::Expr, out: &mut Vec<String>) {
    match &e.kind {
        E::Name(n) => out.push(n.clone()),
        E::Field(b, _) | E::TupleField(b, _) | E::Unary(_, b) | E::Cast(b, _) | E::Try(b) | E::Move(b) | E::Comptime(b) => collect_names(b, out),
        E::Call(c, args) => {
            collect_names(c, out);
            for a in args {
                collect_names(a, out);
            }
        }
        E::Index(a, b) | E::Binary(_, a, b) | E::ArrayRepeat(a, b) => {
            collect_names(a, out);
            collect_names(b, out);
        }
        E::StructLit(_, fs) => {
            for f in fs {
                collect_names(&f.1, out);
            }
        }
        E::Tuple(xs) | E::Array(xs) => {
            for x in xs {
                collect_names(x, out);
            }
        }
        E::Block(b) | E::Unsafe(b) | E::Loop(b) => collect_names_block(b, out),
        E::If(c, t, e2) => {
            collect_names(c, out);
            collect_names_block(t, out);
            if let Some(e2) = e2 {
                collect_names(e2, out);
            }
        }
        E::Match(s, arms) => {
            collect_names(s, out);
            for a in arms {
                if let Some(g) = &a.guard {
                    collect_names(g, out);
                }
                collect_names(&a.body, out);
            }
        }
        E::While(c, b) => {
            collect_names(c, out);
            collect_names_block(b, out);
        }
        E::For(_, _, it, b) => {
            collect_names(it, out);
            collect_names_block(b, out);
        }
        E::Lambda(_, _, b) => collect_names_block(b, out),
        E::Return(Some(v)) => collect_names(v, out),
        E::Range(a, b) => {
            if let Some(a) = a {
                collect_names(a, out);
            }
            if let Some(b) = b {
                collect_names(b, out);
            }
        }
        _ => {}
    }
}

impl From<Diag> for String {
    fn from(d: Diag) -> String {
        d.msg
    }
}
