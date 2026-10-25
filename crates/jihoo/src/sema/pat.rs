// Patterns: `match`, destructuring `let`, and exhaustiveness.
//
// A `match` on a place borrows it: bindings are borrows (or copies of plain
// values). A `match` on a new value owns it: bindings move out of it, and
// the parts no binding takes are dropped in the arm. `match &place` borrows
// mutably, so bindings can change the place.

use super::body::{Fb, Val, VarKind, VK};
use super::{ty_err, Sema, R};
use crate::ast::{self, ExprKind as E, PatKind};
use crate::diag::Span;
use crate::lex::Op;
use crate::mir::*;
use crate::types::{self, TyId, TyKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindMode {
    /// Borrow a place (copy plain values); own a new value.
    Auto,
    Owned,
    Borrow,
    BorrowMut,
}

/// Patterns reduced to constructors, for exhaustiveness.
#[derive(Clone, Debug)]
enum P {
    Wild,
    /// A constructor (a variant, the one constructor of a struct or tuple,
    /// `false`/`true`) and its fields.
    Ctor(u32, Vec<P>),
    /// A value of an infinite domain (integers, strings).
    Lit,
}

impl<'a> Sema<'a> {
    pub fn match_expr(&mut self, fb: &mut Fb, scrut: &ast::Expr, arms: &[ast::Arm], exp: Option<TyId>, span: Span) -> R<Val> {
        let (place, ty, mode) = if let E::Unary(ast::UnOp::Addr, inner) = &scrut.kind {
            // `match &x`: borrows x (mutably, if it can change).
            let v = self.expr_mut(fb, inner)?;
            let VK::Place(p) = v.vk else { return ty_err(inner.span, "`match &` needs a place") };
            let m = if self.place_mutable(fb, &p) { BindMode::BorrowMut } else { BindMode::Borrow };
            (p, v.ty, m)
        } else {
            let v = self.expr(fb, scrut, None)?;
            if v.ty == types::NEVER {
                return Ok(Val::never());
            }
            // A new value is owned; so is a whole owned variable whose
            // parts the arms bind (it is used up, as in Rust).
            let whole_owned = match &v.vk {
                VK::Place(p) => {
                    p.proj.is_empty()
                        && !self.types.is_ref(fb.ty_of(p.local))
                        && self.types.needs_drop(v.ty)
                        && arms.iter().any(|a| super::pat::pat_binds(&a.pat))
                }
                _ => false,
            };
            let owned = v.temp || matches!(v.vk, VK::Op(_)) || whole_owned;
            let t = v.ty;
            if owned {
                let o = self.operand(fb, v, scrut.span)?;
                let tmp = fb.temp(t, scrut.span);
                fb.assign(Place::local(tmp), Rvalue::Use(o), scrut.span);
                (Place::local(tmp), t, BindMode::Owned)
            } else {
                let VK::Place(p) = v.vk else { unreachable!() };
                (p, t, BindMode::Borrow)
            }
        };
        self.check_exhaustive(fb, arms, ty, span)?;
        let want = exp != Some(types::UNIT);
        let result = fb.new_local(types::UNIT, None, true, LocalKind::Temp, span);
        fb.add_temp_local(result);
        let mut rty: Option<TyId> = if want { exp.filter(|&t| t != types::NEVER) } else { Some(types::UNIT) };
        let done = fb.new_block();
        for arm in arms {
            let fail = fb.new_block();
            self.test_pat(fb, &arm.pat, place.clone(), ty, fail)?;
            fb.push_scope(false);
            if let Some(g) = &arm.guard {
                // The guard sees borrows; owned bindings move after it holds.
                let gmode = if mode == BindMode::Owned { BindMode::Borrow } else { mode };
                fb.push_scope(false);
                self.bind(fb, &arm.pat, place.clone(), ty, gmode)?;
                let gv = self.expr(fb, g, Some(types::BOOL))?;
                let gv = self.coerce(fb, gv, types::BOOL, g.span)?;
                let go = self.operand(fb, gv, g.span)?;
                let c = fb.new_local(types::BOOL, None, true, LocalKind::Temp, g.span);
                fb.assign(Place::local(c), Rvalue::Use(go), g.span);
                let pass = fb.new_block();
                let reject = fb.new_block();
                self.pop_scope(fb);
                fb.term(Term::Switch { discr: Operand::Copy(Place::local(c)), targets: vec![(0, reject)], otherwise: pass });
                fb.switch_to(reject);
                // Leave the arm scope (nothing bound in it yet).
                fb.goto(fail);
                fb.switch_to(pass);
            }
            self.bind(fb, &arm.pat, place.clone(), ty, mode)?;
            if mode == BindMode::Owned && self.types.needs_drop(ty) {
                self.drop_rest(fb, &arm.pat, place.clone(), ty, arm.span)?;
                fb.push(Stmt::Forget(place.local));
            }
            fb.push_scope(true);
            let bv = self.expr(fb, &arm.body, if want { rty } else { Some(types::UNIT) })?;
            if bv.ty != types::NEVER {
                if want {
                    let bv = match rty {
                        Some(t) => self.coerce(fb, bv, t, arm.body.span)?,
                        None => bv,
                    };
                    if rty.is_none() {
                        rty = Some(bv.ty);
                    }
                    if bv.ty != types::UNIT {
                        fb.body.locals[result as usize].ty = bv.ty;
                        let o = self.operand(fb, bv, arm.body.span)?;
                        fb.assign(Place::local(result), Rvalue::Use(o), arm.span);
                    }
                } else {
                    self.discard_val(fb, bv, arm.body.span)?;
                }
            }
            self.pop_scope(fb);
            self.pop_scope(fb);
            fb.goto(done);
            fb.switch_to(fail);
        }
        // Exhaustiveness was checked: no value gets here.
        fb.term(Term::Unreachable);
        fb.switch_to(done);
        match rty {
            None => {
                fb.term(Term::Unreachable);
                Ok(Val::never())
            }
            Some(t) if t == types::UNIT || !want => Ok(Val::unit()),
            Some(t) => {
                fb.body.locals[result as usize].ty = t;
                Ok(Val { vk: VK::Place(Place::local(result)), ty: t, temp: true })
            }
        }
    }

    fn discard_val(&mut self, fb: &mut Fb, v: Val, span: Span) -> R<()> {
        if let VK::Op(Operand::Move(_)) = &v.vk {
            let t = fb.temp(v.ty, span);
            let o = self.operand(fb, v, span)?;
            fb.assign(Place::local(t), Rvalue::Use(o), span);
        }
        Ok(())
    }

    /// `let pattern = value`.
    pub fn destructure(&mut self, fb: &mut Fb, pat: &ast::Pat, v: Val, mode: BindMode, span: Span) -> R<()> {
        let ty = v.ty;
        // The pattern must match every value.
        let p = self.reduce(fb, pat, ty)?;
        if let Some(w) = self.useful(&[vec![p]], &[P::Wild], &[ty])? {
            return ty_err(pat.span, &format!("this pattern does not match every value; `{}` is not covered (use `match`)", self.show_witness(&w[0], ty)));
        }
        let owned = match mode {
            BindMode::Auto => v.temp || matches!(v.vk, VK::Op(_)),
            BindMode::Owned => true,
            _ => false,
        };
        if owned {
            let place = match v.vk.clone() {
                VK::Place(p) if v.temp && p.proj.is_empty() => p,
                _ => {
                    let o = self.operand(fb, v, span)?;
                    let tmp = fb.temp(ty, span);
                    fb.assign(Place::local(tmp), Rvalue::Use(o), span);
                    Place::local(tmp)
                }
            };
            self.bind(fb, pat, place.clone(), ty, BindMode::Owned)?;
            if self.types.needs_drop(ty) {
                self.drop_rest(fb, pat, place.clone(), ty, span)?;
                fb.push(Stmt::Forget(place.local));
            }
            Ok(())
        } else {
            let (place, _) = self.as_place(fb, v, span);
            let m = if mode == BindMode::BorrowMut { BindMode::BorrowMut } else { BindMode::Borrow };
            self.bind(fb, pat, place, ty, m)
        }
    }

    /// The enum variant a pattern path names, checking any type prefix.
    fn pat_variant(&mut self, fb: &Fb, path: &[String], ty: TyId, span: Span) -> R<Option<u32>> {
        let Some(vs) = self.types.variants(ty) else { return Ok(None) };
        let name = path.last().unwrap();
        let Some(i) = vs.iter().position(|v| &v.name == name) else {
            if path.len() == 1 {
                return Ok(None);
            }
            return ty_err(span, &format!("`{}` has no variant `{}`", self.types.show(ty), name));
        };
        if path.len() > 1 {
            let head = &path[..path.len() - 1];
            let env = fb.env.clone();
            let ok = match self.lookup_path(env.module, head) {
                Some((super::Sym::Adt(d), _)) => self.types.adt_of(ty).map(|a| a.decl == d).unwrap_or(false),
                _ => self.path_is_type(head, &env) && self.resolve_path_ty_pub(head, &env, span).ok() == Some(ty),
            };
            if !ok {
                return ty_err(span, &format!("this pattern is for `{}`, but the value is a `{}`", head.join("."), self.types.show(ty)));
            }
        }
        Ok(Some(i as u32))
    }

    /// The place a `Box` (or anything with `deref`) points to, when a
    /// pattern looks inside it.
    fn deref_for_pat(&mut self, fb: &mut Fb, pat: &ast::Pat, place: Place, ty: TyId, span: Span) -> R<Option<(Place, TyId)>> {
        let structural = matches!(pat.kind, PatKind::Variant(..) | PatKind::Struct(..) | PatKind::Tuple(..));
        let fits = match (&pat.kind, self.types.kind(ty)) {
            (PatKind::Tuple(_), TyKind::Tuple(_)) => true,
            (PatKind::Variant(..), _) => self.types.variants(ty).is_some(),
            (PatKind::Struct(..), TyKind::Adt(_)) => self.types.variants(ty).is_none() && self.find_method(ty, "deref")?.is_none(),
            _ => false,
        };
        if !structural || fits || self.types.adt_of(ty).is_none() || self.find_method(ty, "deref")?.is_none() {
            return Ok(None);
        }
        let v = self.method_call_val(fb, Val::place(place, ty), "deref", vec![], span, None)?;
        let t = v.ty;
        let VK::Place(p) = v.vk else { return Ok(None) };
        Ok(Some((p, t)))
    }

    /// Jumps to `fail` unless the place matches the pattern.
    fn test_pat(&mut self, fb: &mut Fb, pat: &ast::Pat, place: Place, ty: TyId, fail: BlockId) -> R<()> {
        let span = pat.span;
        if let Some((p, t)) = self.deref_for_pat(fb, pat, place.clone(), ty, span)? {
            return self.test_pat(fb, pat, p, t, fail);
        }
        match &pat.kind {
            PatKind::Wild => Ok(()),
            PatKind::Name(n, _) => {
                if self.names_variant(fb, n, ty) {
                    let v = self.pat_variant(fb, std::slice::from_ref(n), ty, span)?.unwrap();
                    self.test_discr(fb, place, v, fail, span);
                }
                Ok(())
            }
            PatKind::Int(v) => {
                if !self.types.is_int(ty) {
                    return ty_err(span, &format!("an integer pattern cannot match a `{}`", self.types.show(ty)));
                }
                if !self.int_fits(*v, ty) {
                    return ty_err(span, &format!("{} does not fit in `{}`", v, self.types.show(ty)));
                }
                self.test_eq(fb, place, Const::Int(*v, ty), ty, fail, span);
                Ok(())
            }
            PatKind::Char(c) => {
                if !self.types.is_int(ty) {
                    return ty_err(span, &format!("a character pattern cannot match a `{}`", self.types.show(ty)));
                }
                self.test_eq(fb, place, Const::Int(*c as i128, ty), ty, fail, span);
                Ok(())
            }
            PatKind::Bool(b) => {
                if ty != types::BOOL {
                    return ty_err(span, &format!("a bool pattern cannot match a `{}`", self.types.show(ty)));
                }
                let ok = fb.new_block();
                let (t, f) = if *b { (ok, fail) } else { (fail, ok) };
                fb.term(Term::Switch { discr: Operand::Copy(place), targets: vec![(0, f)], otherwise: t });
                fb.switch_to(ok);
                Ok(())
            }
            PatKind::Range(lo, hi) => {
                if !self.types.is_int(ty) {
                    return ty_err(span, &format!("a range pattern cannot match a `{}`", self.types.show(ty)));
                }
                let c1 = fb.temp(types::BOOL, span);
                fb.assign(Place::local(c1), Rvalue::Bin(Op::Ge, Operand::Copy(place.clone()), Operand::Const(Const::Int(*lo, ty))), span);
                let ok1 = fb.new_block();
                fb.term(Term::Switch { discr: Operand::Copy(Place::local(c1)), targets: vec![(0, fail)], otherwise: ok1 });
                fb.switch_to(ok1);
                let c2 = fb.temp(types::BOOL, span);
                fb.assign(Place::local(c2), Rvalue::Bin(Op::Le, Operand::Copy(place), Operand::Const(Const::Int(*hi, ty))), span);
                let ok2 = fb.new_block();
                fb.term(Term::Switch { discr: Operand::Copy(Place::local(c2)), targets: vec![(0, fail)], otherwise: ok2 });
                fb.switch_to(ok2);
                Ok(())
            }
            PatKind::Str(s) => {
                let sv = Val::op(Operand::Const(Const::Str(s.clone())), types::STR);
                let target = if ty == types::STR { Val::place(place, ty) } else { self.coerce(fb, Val::place(place, ty), types::STR, span)? };
                let r = self.method_call_val(fb, target, "eq", vec![sv], span, None)?;
                let o = self.operand(fb, r, span)?;
                let ok = fb.new_block();
                fb.term(Term::Switch { discr: o, targets: vec![(0, fail)], otherwise: ok });
                fb.switch_to(ok);
                Ok(())
            }
            PatKind::Tuple(ps) => {
                let TyKind::Tuple(ts) = self.types.kind(ty).clone() else {
                    return ty_err(span, &format!("a tuple pattern cannot match a `{}`", self.types.show(ty)));
                };
                if ts.len() != ps.len() {
                    return ty_err(span, &format!("this tuple has {} parts, the pattern {}", ts.len(), ps.len()));
                }
                for (i, (p, t)) in ps.iter().zip(ts).enumerate() {
                    self.test_pat(fb, p, place.with(Proj::Field(i as u32)), t, fail)?;
                }
                Ok(())
            }
            PatKind::Struct(path, fields, _) => {
                let fs = self.struct_fields_for_pat(fb, path, ty, span)?;
                for (n, p) in fields {
                    let Some(i) = fs.iter().position(|f| &f.0 == n) else {
                        return ty_err(p.span, &format!("`{}` has no field `{}`", self.types.show(ty), n));
                    };
                    self.test_pat(fb, p, place.with(Proj::Field(i as u32)), fs[i].1, fail)?;
                }
                Ok(())
            }
            PatKind::Variant(path, ps) => {
                let Some(v) = self.pat_variant(fb, path, ty, span)? else {
                    return ty_err(span, &format!("`{}` is not a variant of `{}`", path.join("."), self.types.show(ty)));
                };
                let fields = self.types.variants(ty).unwrap()[v as usize].fields.clone();
                if fields.len() != ps.len() {
                    return ty_err(span, &format!("`{}` has {} field(s), the pattern {}", path.last().unwrap(), fields.len(), ps.len()));
                }
                self.test_discr(fb, place.clone(), v, fail, span);
                for (i, (p, t)) in ps.iter().zip(fields).enumerate() {
                    self.test_pat(fb, p, place.with(Proj::Variant(v)).with(Proj::Field(i as u32)), t, fail)?;
                }
                Ok(())
            }
            PatKind::Or(alts) => {
                if alts.iter().any(pat_binds) {
                    return ty_err(span, "the alternatives of a `|` pattern cannot bind names yet");
                }
                let ok = fb.new_block();
                for (i, a) in alts.iter().enumerate() {
                    let next = if i + 1 == alts.len() { fail } else { fb.new_block() };
                    self.test_pat(fb, a, place.clone(), ty, next)?;
                    fb.goto(ok);
                    if next != fail {
                        fb.switch_to(next);
                    }
                }
                fb.switch_to(ok);
                Ok(())
            }
        }
    }

    fn struct_fields_for_pat(&mut self, fb: &Fb, path: &[String], ty: TyId, span: Span) -> R<Vec<(String, TyId)>> {
        let Some(a) = self.types.adt_of(ty) else { return ty_err(span, &format!("a struct pattern cannot match a `{}`", self.types.show(ty))) };
        let decl = a.decl;
        let types::AdtBody::Struct(fs) = a.body.clone() else { return ty_err(span, &format!("`{}` is not a struct", self.types.show(ty))) };
        let env = fb.env.clone();
        let ok = match self.lookup_path(env.module, path) {
            Some((super::Sym::Adt(d), _)) => d == decl,
            _ => path.len() == 1 && path[0] == "Self" && env.self_ty == Some(ty),
        };
        if !ok {
            return ty_err(span, &format!("this pattern is for `{}`, but the value is a `{}`", path.join("."), self.types.show(ty)));
        }
        Ok(fs.into_iter().map(|f| (f.name, f.ty)).collect())
    }

    fn test_discr(&mut self, fb: &mut Fb, place: Place, v: u32, fail: BlockId, span: Span) {
        let d = fb.temp(types::I64, span);
        fb.assign(Place::local(d), Rvalue::Discriminant(place), span);
        let ok = fb.new_block();
        fb.term(Term::Switch { discr: Operand::Copy(Place::local(d)), targets: vec![(v as i128, ok)], otherwise: fail });
        fb.switch_to(ok);
    }

    fn test_eq(&mut self, fb: &mut Fb, place: Place, c: Const, ty: TyId, fail: BlockId, _span: Span) {
        let Const::Int(v, _) = c else { unreachable!() };
        let _ = ty;
        let ok = fb.new_block();
        fb.term(Term::Switch { discr: Operand::Copy(place), targets: vec![(v, ok)], otherwise: fail });
        fb.switch_to(ok);
    }

    /// Makes the pattern's variables, for a place known to match.
    fn bind(&mut self, fb: &mut Fb, pat: &ast::Pat, place: Place, ty: TyId, mode: BindMode) -> R<()> {
        let span = pat.span;
        if let Some((p, t)) = self.deref_for_pat(fb, pat, place.clone(), ty, span)? {
            // Inside a box, bindings borrow.
            let m = if mode == BindMode::Owned { BindMode::Borrow } else { mode };
            return self.bind(fb, pat, p, t, m);
        }
        match &pat.kind {
            PatKind::Name(n, var) => {
                if self.names_variant(fb, n, ty) {
                    return Ok(());
                }
                // A borrow held as a value (`Option(ref T)`'s payload): the
                // variable is what it points to.
                if self.types.is_ref(ty) && matches!(mode, BindMode::Owned | BindMode::Auto | BindMode::Borrow) {
                    let o = if matches!(self.types.kind(ty), TyKind::RefMut(_)) && mode != BindMode::Borrow { Operand::Move(place) } else { Operand::Copy(place) };
                    let l = fb.declare(n, ty, false, VarKind::Borrow, span);
                    fb.assign(Place::local(l), Rvalue::Use(o), span);
                    return Ok(());
                }
                match mode {
                    BindMode::Owned | BindMode::Auto => {
                        let v = Val { vk: VK::Place(place), ty, temp: true };
                        let o = self.operand(fb, v, span)?;
                        let l = fb.declare(n, ty, *var, VarKind::Owned, span);
                        fb.assign(Place::local(l), Rvalue::Use(o), span);
                    }
                    BindMode::Borrow => {
                        if self.types.is_plain(ty) {
                            let l = fb.declare(n, ty, *var, VarKind::Owned, span);
                            fb.assign(Place::local(l), Rvalue::Use(Operand::Copy(place)), span);
                        } else {
                            if *var {
                                return ty_err(span, "`var` would copy a value that is not plain; use `.clone()`");
                            }
                            let rt = self.types.refty(ty);
                            let l = fb.declare(n, rt, false, VarKind::Borrow, span);
                            fb.assign(Place::local(l), Rvalue::Ref(place), span);
                        }
                    }
                    BindMode::BorrowMut => {
                        let rt = self.types.refmut(ty);
                        let l = fb.declare(n, rt, false, VarKind::Borrow, span);
                        fb.assign(Place::local(l), Rvalue::RefMut(place), span);
                    }
                }
                Ok(())
            }
            PatKind::Tuple(ps) => {
                let TyKind::Tuple(ts) = self.types.kind(ty).clone() else { return Ok(()) };
                for (i, (p, t)) in ps.iter().zip(ts).enumerate() {
                    self.bind(fb, p, place.with(Proj::Field(i as u32)), t, mode)?;
                }
                Ok(())
            }
            PatKind::Struct(path, fields, _) => {
                let fs = self.struct_fields_for_pat(fb, path, ty, span)?;
                for (n, p) in fields {
                    let i = fs.iter().position(|f| &f.0 == n).unwrap();
                    self.bind(fb, p, place.with(Proj::Field(i as u32)), fs[i].1, mode)?;
                }
                Ok(())
            }
            PatKind::Variant(path, ps) => {
                let v = self.pat_variant(fb, path, ty, span)?.unwrap();
                let fields = self.types.variants(ty).unwrap()[v as usize].fields.clone();
                for (i, (p, t)) in ps.iter().zip(fields).enumerate() {
                    self.bind(fb, p, place.with(Proj::Variant(v)).with(Proj::Field(i as u32)), t, mode)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Drops the parts of an owned value that the pattern's bindings did
    /// not move out.
    fn drop_rest(&mut self, fb: &mut Fb, pat: &ast::Pat, place: Place, ty: TyId, span: Span) -> R<()> {
        if !self.types.needs_drop(ty) {
            return Ok(());
        }
        // Through a box, bindings borrowed: the box itself is dropped.
        let structural = matches!(pat.kind, PatKind::Variant(..) | PatKind::Struct(..) | PatKind::Tuple(..));
        if structural && self.types.adt_of(ty).is_some() && self.types.variants(ty).is_none() && !matches!(pat.kind, PatKind::Struct(..)) {
            fb.push(Stmt::Drop(place, span));
            return Ok(());
        }
        if let PatKind::Struct(..) = &pat.kind {
            if self.find_method(ty, "deref")?.is_some() {
                fb.push(Stmt::Drop(place, span));
                return Ok(());
            }
        }
        match &pat.kind {
            PatKind::Wild | PatKind::Or(_) | PatKind::Int(_) | PatKind::Char(_) | PatKind::Bool(_) | PatKind::Str(_) | PatKind::Range(..) => {
                fb.push(Stmt::Drop(place, span));
                Ok(())
            }
            PatKind::Name(n, _) => {
                if self.names_variant(fb, n, ty) {
                    fb.push(Stmt::Drop(place, span));
                }
                Ok(())
            }
            PatKind::Tuple(ps) => {
                let TyKind::Tuple(ts) = self.types.kind(ty).clone() else { return Ok(()) };
                for (i, (p, t)) in ps.iter().zip(ts).enumerate() {
                    self.drop_rest(fb, p, place.with(Proj::Field(i as u32)), t, span)?;
                }
                Ok(())
            }
            PatKind::Struct(path, fields, _) => {
                if self.types.adt_of(ty).map(|a| a.has_drop).unwrap_or(false) {
                    return ty_err(span, &format!("cannot take apart a `{}`: it has a `Drop` impl", self.types.show(ty)));
                }
                let fs = self.struct_fields_for_pat(fb, path, ty, span)?;
                for (i, (fname, ft)) in fs.iter().enumerate() {
                    let fp = place.with(Proj::Field(i as u32));
                    match fields.iter().find(|(n, _)| n == fname) {
                        Some((_, p)) => self.drop_rest(fb, p, fp, *ft, span)?,
                        None => {
                            if self.types.needs_drop(*ft) {
                                fb.push(Stmt::Drop(fp, span));
                            }
                        }
                    }
                }
                Ok(())
            }
            PatKind::Variant(path, ps) => {
                if self.types.adt_of(ty).map(|a| a.has_drop).unwrap_or(false) {
                    return ty_err(span, &format!("cannot take apart a `{}`: it has a `Drop` impl", self.types.show(ty)));
                }
                let v = self.pat_variant(fb, path, ty, span)?.unwrap();
                let fields = self.types.variants(ty).unwrap()[v as usize].fields.clone();
                for (i, (p, t)) in ps.iter().zip(fields).enumerate() {
                    self.drop_rest(fb, p, place.with(Proj::Variant(v)).with(Proj::Field(i as u32)), t, span)?;
                }
                Ok(())
            }
        }
    }

    // ---- exhaustiveness ----

    fn check_exhaustive(&mut self, fb: &mut Fb, arms: &[ast::Arm], ty: TyId, span: Span) -> R<()> {
        let mut rows = Vec::new();
        for a in arms {
            let p = self.reduce(fb, &a.pat, ty)?;
            // An arm that no value reaches.
            if self.useful(&rows.iter().map(|r: &P| vec![r.clone()]).collect::<Vec<_>>(), std::slice::from_ref(&p), &[ty])?.is_none() {
                return ty_err(a.pat.span, "this arm is never reached: the arms above match everything it matches");
            }
            if a.guard.is_none() {
                rows.push(p);
            }
        }
        let m: Vec<Vec<P>> = rows.into_iter().map(|r| vec![r]).collect();
        if let Some(w) = self.useful(&m, &[P::Wild], &[ty])? {
            return ty_err(span, &format!("this `match` does not cover `{}`", self.show_witness(&w[0], ty)));
        }
        Ok(())
    }

    fn reduce(&mut self, fb: &mut Fb, pat: &ast::Pat, ty: TyId) -> R<P> {
        let span = pat.span;
        // Looking inside a box.
        let structural = matches!(pat.kind, PatKind::Variant(..) | PatKind::Struct(..) | PatKind::Tuple(..));
        if structural {
            let fits = match (&pat.kind, self.types.kind(ty)) {
                (PatKind::Tuple(_), TyKind::Tuple(_)) => true,
                (PatKind::Variant(..), _) => self.types.variants(ty).is_some(),
                (PatKind::Struct(..), TyKind::Adt(_)) => self.types.variants(ty).is_none() && self.find_method(ty, "deref")?.is_none(),
                _ => false,
            };
            if !fits {
                if let Some(t) = self.deref_target(ty)? {
                    let inner = self.reduce(fb, pat, t)?;
                    return Ok(P::Ctor(0, vec![inner]));
                }
            }
        }
        Ok(match &pat.kind {
            PatKind::Wild => P::Wild,
            PatKind::Name(n, _) => {
                if self.names_variant(fb, n, ty) {
                    let v = self.pat_variant(fb, std::slice::from_ref(n), ty, span)?.unwrap();
                    P::Ctor(v, vec![])
                } else {
                    P::Wild
                }
            }
            PatKind::Bool(b) => P::Ctor(*b as u32, vec![]),
            PatKind::Int(_) | PatKind::Char(_) | PatKind::Str(_) | PatKind::Range(..) => P::Lit,
            PatKind::Tuple(ps) => {
                let TyKind::Tuple(ts) = self.types.kind(ty).clone() else {
                    return ty_err(span, &format!("a tuple pattern cannot match a `{}`", self.types.show(ty)));
                };
                if ts.len() != ps.len() {
                    return ty_err(span, &format!("this tuple has {} parts, the pattern {}", ts.len(), ps.len()));
                }
                let mut v = Vec::new();
                for (p, t) in ps.iter().zip(ts) {
                    v.push(self.reduce(fb, p, t)?);
                }
                P::Ctor(0, v)
            }
            PatKind::Struct(path, fields, rest) => {
                let fs = self.struct_fields_for_pat(fb, path, ty, span)?;
                let mut v = vec![P::Wild; fs.len()];
                for (n, p) in fields {
                    let Some(i) = fs.iter().position(|f| &f.0 == n) else {
                        return ty_err(p.span, &format!("`{}` has no field `{}`", self.types.show(ty), n));
                    };
                    v[i] = self.reduce(fb, p, fs[i].1)?;
                }
                if !rest && fields.len() != fs.len() {
                    let missing: Vec<&str> = fs.iter().filter(|f| !fields.iter().any(|(n, _)| n == &f.0)).map(|f| f.0.as_str()).collect();
                    return ty_err(span, &format!("the pattern leaves out {}; add them or `..`", missing.join(", ")));
                }
                P::Ctor(0, v)
            }
            PatKind::Variant(path, ps) => {
                let Some(vi) = self.pat_variant(fb, path, ty, span)? else {
                    return ty_err(span, &format!("`{}` is not a variant of `{}`", path.join("."), self.types.show(ty)));
                };
                let fields = self.types.variants(ty).unwrap()[vi as usize].fields.clone();
                if fields.len() != ps.len() {
                    return ty_err(span, &format!("`{}` has {} field(s), the pattern {}", path.last().unwrap(), fields.len(), ps.len()));
                }
                let mut v = Vec::new();
                for (p, t) in ps.iter().zip(fields) {
                    v.push(self.reduce(fb, p, t)?);
                }
                P::Ctor(vi, v)
            }
            PatKind::Or(alts) => {
                // Represented by trying each alternative as its own row; an
                // or-pattern covers what any alternative covers. Return the
                // first and let `useful` see the rest through expansion.
                let mut out = Vec::new();
                for a in alts {
                    out.push(self.reduce(fb, a, ty)?);
                }
                return Ok(self.or_pat(out));
            }
        })
    }

    fn or_pat(&self, alts: Vec<P>) -> P {
        // Encoded as a constructor 0xffff_ffff whose fields are the
        // alternatives; `useful` expands it.
        P::Ctor(u32::MAX, alts)
    }

    /// The type `deref` points to, for types patterns can see through.
    fn deref_target(&mut self, ty: TyId) -> R<Option<TyId>> {
        if self.types.adt_of(ty).is_none() {
            return Ok(None);
        }
        let Some((fid, iargs)) = self.find_method(ty, "deref")? else { return Ok(None) };
        let id = self.instance(fid, iargs, Span::default())?;
        let r = self.out[id as usize].sig.ret;
        Ok(self.types.pointee(r))
    }

    /// The constructors of a type: `Some(n)` if finite (with arities), or
    /// `None` for infinite domains.
    fn ctors(&mut self, ty: TyId) -> R<Option<Vec<(u32, Vec<TyId>)>>> {
        Ok(match self.types.kind(ty).clone() {
            TyKind::Bool => Some(vec![(0, vec![]), (1, vec![])]),
            TyKind::Tuple(ts) => Some(vec![(0, ts)]),
            TyKind::Adt(_) => {
                if let Some(vs) = self.types.variants(ty) {
                    Some(vs.iter().enumerate().map(|(i, v)| (i as u32, v.fields.clone())).collect())
                } else if let Some(t) = self.deref_target(ty)? {
                    Some(vec![(0, vec![t])])
                } else {
                    Some(vec![(0, self.types.field_tys(ty))])
                }
            }
            _ => None,
        })
    }

    /// Maranget's usefulness: a value matched by `v` and by no row of `m`,
    /// if there is one (the witness).
    fn useful(&mut self, m: &[Vec<P>], v: &[P], tys: &[TyId]) -> R<Option<Vec<P>>> {
        // Expand or-patterns in the first column.
        if let Some(P::Ctor(u32::MAX, alts)) = v.first() {
            for a in alts.clone() {
                let mut v2 = vec![a];
                v2.extend_from_slice(&v[1..]);
                if let Some(w) = self.useful(m, &v2, tys)? {
                    return Ok(Some(w));
                }
            }
            return Ok(None);
        }
        let mut m2: Vec<Vec<P>> = Vec::new();
        for row in m {
            if let Some(P::Ctor(u32::MAX, alts)) = row.first() {
                for a in alts {
                    let mut r = vec![a.clone()];
                    r.extend_from_slice(&row[1..]);
                    m2.push(r);
                }
            } else {
                m2.push(row.clone());
            }
        }
        let m = &m2;
        if v.is_empty() {
            return Ok(if m.is_empty() { Some(vec![]) } else { None });
        }
        let ty = tys[0];
        match &v[0] {
            P::Ctor(c, fields) => {
                let arity = fields.len();
                let ftys = self.ctor_field_tys(ty, *c)?;
                let sm = specialize(m, *c, arity);
                let mut sv = fields.clone();
                sv.extend_from_slice(&v[1..]);
                let mut st = ftys.clone();
                st.extend_from_slice(&tys[1..]);
                Ok(self.useful(&sm, &sv, &st)?.map(|w| {
                    let (fs, rest) = w.split_at(arity);
                    let mut out = vec![P::Ctor(*c, fs.to_vec())];
                    out.extend_from_slice(rest);
                    out
                }))
            }
            P::Lit => {
                // A literal is useful if the rows without it (wildcards) do
                // not cover the rest.
                let dm = default_rows(m);
                Ok(self.useful(&dm, &v[1..], &tys[1..])?.map(|w| {
                    let mut out = vec![P::Lit];
                    out.extend(w);
                    out
                }))
            }
            P::Wild => {
                let present: Vec<u32> = m.iter().filter_map(|r| match &r[0] {
                    P::Ctor(c, _) => Some(*c),
                    _ => None,
                }).collect();
                let all = self.ctors(ty)?;
                if let Some(all) = all {
                    let complete = all.iter().all(|(c, _)| present.contains(c));
                    if complete {
                        for (c, ftys) in all {
                            let arity = ftys.len();
                            let sm = specialize(m, c, arity);
                            let mut sv = vec![P::Wild; arity];
                            sv.extend_from_slice(&v[1..]);
                            let mut st = ftys.clone();
                            st.extend_from_slice(&tys[1..]);
                            if let Some(w) = self.useful(&sm, &sv, &st)? {
                                let (fs, rest) = w.split_at(arity);
                                let mut out = vec![P::Ctor(c, fs.to_vec())];
                                out.extend_from_slice(rest);
                                return Ok(Some(out));
                            }
                        }
                        return Ok(None);
                    }
                    let dm = default_rows(m);
                    return Ok(self.useful(&dm, &v[1..], &tys[1..])?.map(|w| {
                        let missing = all.iter().find(|(c, _)| !present.contains(c)).map(|(c, f)| P::Ctor(*c, vec![P::Wild; f.len()])).unwrap_or(P::Wild);
                        let mut out = vec![missing];
                        out.extend(w);
                        out
                    }));
                }
                let dm = default_rows(m);
                Ok(self.useful(&dm, &v[1..], &tys[1..])?.map(|w| {
                    let mut out = vec![P::Wild];
                    out.extend(w);
                    out
                }))
            }
        }
    }

    fn ctor_field_tys(&mut self, ty: TyId, c: u32) -> R<Vec<TyId>> {
        Ok(match self.ctors(ty)? {
            Some(all) => all.into_iter().find(|x| x.0 == c).map(|x| x.1).unwrap_or_default(),
            None => vec![],
        })
    }

    fn show_witness(&mut self, p: &P, ty: TyId) -> String {
        match p {
            P::Wild | P::Lit => "_".into(),
            P::Ctor(c, fs) => {
                let kind = self.types.kind(ty).clone();
                match kind {
                    TyKind::Bool => (*c == 1).to_string(),
                    TyKind::Tuple(ts) => {
                        let parts: Vec<String> = fs.iter().zip(ts).map(|(f, t)| self.show_witness(f, t)).collect();
                        format!("({})", parts.join(", "))
                    }
                    _ => {
                        if let Some(vs) = self.types.variants(ty).cloned() {
                            let v = &vs[*c as usize];
                            if fs.is_empty() {
                                v.name.clone()
                            } else {
                                let parts: Vec<String> = fs.iter().zip(v.fields.clone()).map(|(f, t)| self.show_witness(f, t)).collect();
                                format!("{}({})", v.name, parts.join(", "))
                            }
                        } else if let Ok(Some(t)) = self.deref_target(ty) {
                            self.show_witness(&fs[0], t)
                        } else {
                            let name = self.types.show(ty);
                            format!("{} {{ .. }}", name)
                        }
                    }
                }
            }
        }
    }
}

fn specialize(m: &[Vec<P>], c: u32, arity: usize) -> Vec<Vec<P>> {
    let mut out = Vec::new();
    for row in m {
        match &row[0] {
            P::Ctor(rc, fs) if *rc == c => {
                let mut r = fs.clone();
                r.extend_from_slice(&row[1..]);
                out.push(r);
            }
            P::Wild => {
                let mut r = vec![P::Wild; arity];
                r.extend_from_slice(&row[1..]);
                out.push(r);
            }
            _ => {}
        }
    }
    out
}

fn default_rows(m: &[Vec<P>]) -> Vec<Vec<P>> {
    m.iter().filter(|r| matches!(r[0], P::Wild)).map(|r| r[1..].to_vec()).collect()
}

pub fn pat_binds(p: &ast::Pat) -> bool {
    match &p.kind {
        // Capitalized names are taken for variants.
        PatKind::Name(n, _) => !n.starts_with(|c: char| c.is_ascii_uppercase()),
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::Or(ps) => ps.iter().any(pat_binds),
        PatKind::Struct(_, fs, _) => fs.iter().any(|f| pat_binds(&f.1)),
        _ => false,
    }
}
