// Built-in functions: what the compiler itself must provide. Everything
// else is library code.

use super::body::{Fb, Val, VK};
use super::{ty_err, Sema, R};
use crate::ast;
use crate::diag::Span;
use crate::mir::*;
use crate::types::{self, TyId, TyKind};

impl<'a> Sema<'a> {
    pub fn builtin_call(&mut self, fb: &mut Fb, n: &str, args: &[ast::Expr], exp: Option<TyId>, span: Span) -> R<Option<Val>> {
        let env = fb.env.clone();
        let need_unsafe = |fb: &Fb| -> R<()> {
            if fb.unsafe_depth == 0 {
                return ty_err(span, &format!("`{}` is only allowed in `unsafe` code", n));
            }
            Ok(())
        };
        let arity = |k: usize| -> R<()> {
            if args.len() != k {
                return ty_err(span, &format!("`{}` takes {} argument(s), {} given", n, k, args.len()));
            }
            Ok(())
        };
        let v = match n {
            "size_of" | "align_of" => {
                arity(1)?;
                let t = self.expr_ty(&args[0], &env)?;
                let l = self.types.layout(t);
                let rt = exp.filter(|&t| self.types.is_int(t)).unwrap_or(types::I64);
                Val::op(Operand::Const(Const::Int(if n == "size_of" { l.size } else { l.align } as i128, rt)), rt)
            }
            "type_name" => {
                arity(1)?;
                let t = self.expr_ty(&args[0], &env)?;
                let s = self.types.show(t);
                self.view_ty(TyKind::Str);
                Val::op(Operand::Const(Const::Str(s.into_bytes())), types::STR)
            }
            "needs_drop" => {
                arity(1)?;
                let t = self.expr_ty(&args[0], &env)?;
                let b = self.types.needs_drop(t);
                Val::op(Operand::Const(Const::Bool(b)), types::BOOL)
            }
            "trap" => {
                arity(0)?;
                self.emit_call(fb, Callee::Intrinsic(Intrinsic::Trap), vec![], types::NEVER, span)?
            }
            "syscall" => {
                need_unsafe(fb)?;
                if args.is_empty() || args.len() > 7 {
                    return ty_err(span, "`syscall` takes the number and up to 6 arguments");
                }
                let mut ops = Vec::new();
                for a in args {
                    let v = self.expr(fb, a, Some(types::I64))?;
                    let o = match self.types.kind(v.ty) {
                        TyKind::Int(_) | TyKind::Ptr(_) | TyKind::Bool => {
                            let t = v.ty;
                            let o = self.operand(fb, v, a.span)?;
                            if t == types::I64 {
                                o
                            } else {
                                let c = self.rvalue(fb, Rvalue::Cast(o, types::I64, CastKind::Numeric), types::I64, a.span);
                                Operand::Copy(self.place_of_val(c))
                            }
                        }
                        _ => return ty_err(a.span, "`syscall` arguments are integers and pointers"),
                    };
                    ops.push(o);
                }
                self.emit_call(fb, Callee::Intrinsic(Intrinsic::Syscall), ops, types::I64, span)?
            }
            "mem_copy" => {
                // mem_copy(dst: *T, src: *T, n: i64): copies n elements.
                need_unsafe(fb)?;
                arity(3)?;
                let d = self.expr(fb, &args[0], None)?;
                let Some(et) = self.types.pointee(d.ty).filter(|_| self.types.is_ptr(d.ty)) else {
                    return ty_err(args[0].span, "`mem_copy` copies between pointers");
                };
                let dt = d.ty;
                let s = self.expr(fb, &args[1], Some(dt))?;
                let s = self.coerce(fb, s, dt, args[1].span)?;
                let c = self.expr(fb, &args[2], Some(types::I64))?;
                let c = self.coerce(fb, c, types::I64, args[2].span)?;
                let ops = vec![self.operand(fb, d, span)?, self.operand(fb, s, span)?, self.operand(fb, c, span)?];
                self.emit_call(fb, Callee::Intrinsic(Intrinsic::Copy(et)), ops, types::UNIT, span)?
            }
            "mem_fill" => {
                need_unsafe(fb)?;
                arity(3)?;
                let pu8 = self.types.ptr(types::U8);
                let d = self.expr(fb, &args[0], Some(pu8))?;
                let d = if self.types.is_ptr(d.ty) && d.ty != pu8 {
                    let o = self.operand(fb, d, span)?;
                    self.rvalue(fb, Rvalue::Cast(o, pu8, CastKind::Ptr), pu8, span)
                } else {
                    self.coerce(fb, d, pu8, args[0].span)?
                };
                let b = self.expr(fb, &args[1], Some(types::U8))?;
                let b = self.coerce(fb, b, types::U8, args[1].span)?;
                let c = self.expr(fb, &args[2], Some(types::I64))?;
                let c = self.coerce(fb, c, types::I64, args[2].span)?;
                let ops = vec![self.operand(fb, d, span)?, self.operand(fb, b, span)?, self.operand(fb, c, span)?];
                self.emit_call(fb, Callee::Intrinsic(Intrinsic::Fill), ops, types::UNIT, span)?
            }
            "read" => {
                // read(p: *T) -> T: the value at p, which the caller now owns.
                need_unsafe(fb)?;
                arity(1)?;
                let p = self.expr(fb, &args[0], None)?;
                let Some(et) = self.types.pointee(p.ty).filter(|_| self.types.is_ptr(p.ty)) else {
                    return ty_err(args[0].span, "`read` reads through a pointer");
                };
                let o = self.operand(fb, p, span)?;
                let pet = self.types.ptr(et);
                let pl = self.operand_local(fb, o, pet, span);
                self.rvalue(fb, Rvalue::Use(Operand::Copy(Place::deref(pl))), et, span)
            }
            "write" => {
                // write(p: *T, v: T): stores v at p without dropping what was there.
                need_unsafe(fb)?;
                arity(2)?;
                let p = self.expr(fb, &args[0], None)?;
                let Some(et) = self.types.pointee(p.ty).filter(|_| self.types.is_ptr(p.ty)) else {
                    return ty_err(args[0].span, "`write` writes through a pointer");
                };
                let o = self.operand(fb, p, span)?;
                let pt = self.types.ptr(et);
                let pl = self.operand_local(fb, o, pt, span);
                let v = self.expr(fb, &args[1], Some(et))?;
                let v = self.coerce(fb, v, et, args[1].span)?;
                let vo = self.operand(fb, v, args[1].span)?;
                fb.assign(Place::deref(pl), Rvalue::Use(vo), span);
                Val::unit()
            }
            "forget" => {
                // forget(v): v's destructor does not run.
                arity(1)?;
                let v = self.expr(fb, &args[0], None)?;
                let t = v.ty;
                let o = self.operand(fb, v, span)?;
                let tmp = fb.temp(t, span);
                fb.assign(Place::local(tmp), Rvalue::Use(o), span);
                fb.push(Stmt::Forget(tmp));
                Val::unit()
            }
            "make_slice" | "make_str" => {
                // make_slice(p: *T, n: i64) -> [T]: a view of n elements at p.
                need_unsafe(fb)?;
                arity(2)?;
                let pu8 = self.types.ptr(types::U8);
                let p = self.expr(fb, &args[0], if n == "make_str" { Some(pu8) } else { None })?;
                let Some(et) = self.types.pointee(p.ty).filter(|_| self.types.is_ptr(p.ty)) else {
                    return ty_err(args[0].span, "expected a pointer");
                };
                if n == "make_str" && et != types::U8 {
                    return ty_err(args[0].span, "`make_str` takes a `*u8`");
                }
                let c = self.expr(fb, &args[1], Some(types::I64))?;
                let c = self.coerce(fb, c, types::I64, args[1].span)?;
                let vt = if n == "make_str" { self.view_ty(TyKind::Str) } else { self.view_ty(TyKind::Slice(et)) };
                let ops = vec![self.operand(fb, p, span)?, self.operand(fb, c, span)?];
                self.rvalue(fb, Rvalue::Aggregate(Agg::View(vt), ops), vt, span)
            }
            "zeroed" => {
                need_unsafe(fb)?;
                arity(1)?;
                let t = self.expr_ty(&args[0], &env)?;
                Val::op(Operand::Const(Const::Zeroed(t)), t)
            }
            "sqrt" | "floor" | "ceil" | "trunc" | "round" | "abs" => {
                arity(1)?;
                let v = self.expr(fb, &args[0], exp.filter(|&t| self.types.is_float(t)))?;
                let t = v.ty;
                if !self.types.is_float(t) {
                    if n == "abs" && self.types.int(t).map(|i| i.signed).unwrap_or(false) {
                        let o = self.operand(fb, v, span)?;
                        return Ok(Some(self.emit_call(fb, Callee::Intrinsic(Intrinsic::Abs(t)), vec![o], t, span)?));
                    }
                    return ty_err(args[0].span, &format!("`{}` takes a float", n));
                }
                let o = self.operand(fb, v, span)?;
                let i = match n {
                    "sqrt" => Intrinsic::Sqrt(t),
                    "floor" => Intrinsic::Floor(t),
                    "ceil" => Intrinsic::Ceil(t),
                    "trunc" => Intrinsic::Trunc(t),
                    "round" => Intrinsic::Round(t),
                    _ => Intrinsic::Abs(t),
                };
                self.emit_call(fb, Callee::Intrinsic(i), vec![o], t, span)?
            }
            "copysign" => {
                arity(2)?;
                let a = self.expr(fb, &args[0], exp.filter(|&t| self.types.is_float(t)))?;
                let t = a.ty;
                if !self.types.is_float(t) {
                    return ty_err(args[0].span, "`copysign` takes floats");
                }
                let b = self.expr(fb, &args[1], Some(t))?;
                let b = self.coerce(fb, b, t, args[1].span)?;
                let ops = vec![self.operand(fb, a, span)?, self.operand(fb, b, span)?];
                self.emit_call(fb, Callee::Intrinsic(Intrinsic::Copysign(t)), ops, t, span)?
            }
            "argc" => {
                arity(0)?;
                self.emit_call(fb, Callee::Intrinsic(Intrinsic::Argc), vec![], types::I64, span)?
            }
            "argv" => {
                arity(0)?;
                let pu8 = self.types.ptr(types::U8);
                let ppu8 = self.types.ptr(pu8);
                self.emit_call(fb, Callee::Intrinsic(Intrinsic::Argv), vec![], ppu8, span)?
            }
            "atomic_load" | "atomic_store" | "atomic_swap" | "atomic_add" | "atomic_sub" | "atomic_and" | "atomic_or" | "atomic_xor"
            | "atomic_cas" => {
                need_unsafe(fb)?;
                let p = self.expr(fb, args.first().ok_or_else(|| crate::diag::Diag::new(span, "missing pointer"))?, None)?;
                let Some(et) = self.types.pointee(p.ty).filter(|_| self.types.is_ptr(p.ty)) else {
                    return ty_err(args[0].span, "atomics work through a pointer");
                };
                if !self.types.is_int(et) && !self.types.is_ptr(et) && et != types::BOOL {
                    return ty_err(args[0].span, "atomics work on integers, bools and pointers");
                }
                let mut ops = vec![self.operand(fb, p, span)?];
                let want = match n {
                    "atomic_load" => 1,
                    "atomic_cas" => 3,
                    _ => 2,
                };
                arity(want)?;
                for a in &args[1..] {
                    let v = self.expr(fb, a, Some(et))?;
                    let v = self.coerce(fb, v, et, a.span)?;
                    ops.push(self.operand(fb, v, a.span)?);
                }
                let (i, rt) = match n {
                    "atomic_load" => (Intrinsic::AtomicLoad(et), et),
                    "atomic_store" => (Intrinsic::AtomicStore(et), types::UNIT),
                    "atomic_cas" => (Intrinsic::AtomicCas(et), types::BOOL),
                    _ => (Intrinsic::AtomicRmw(n["atomic_".len()..].to_string(), et), et),
                };
                self.emit_call(fb, Callee::Intrinsic(i), ops, rt, span)?
            }
            "fence" => {
                arity(0)?;
                self.emit_call(fb, Callee::Intrinsic(Intrinsic::Fence), vec![], types::UNIT, span)?
            }
            _ => return Ok(None),
        };
        let _ = VK::Op(Operand::Const(Const::Bool(true)));
        Ok(Some(v))
    }
}
