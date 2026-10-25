// Constant expressions that sema folds itself: literals, constants,
// compile-time parameters, arithmetic, `size_of`. Anything more runs on the
// interpreter.

use super::{ty_err, CVal, Env, Sema, Sym, R};
use crate::ast::{self, ExprKind as E};
use crate::lex::Op;
use crate::mir::Const;
use crate::types::{self, TyId, TyKind};

impl<'a> Sema<'a> {
    pub fn const_int(&mut self, e: &ast::Expr, env: &Env) -> R<i128> {
        match self.const_expr(e, env, Some(types::I64))? {
            (Const::Int(v, _), _) => Ok(v),
            _ => ty_err(e.span, "expected a compile-time integer"),
        }
    }

    /// Whether `v` is a value of `t`. A 128-bit constant is its value's bit
    /// pattern (a `u128` past `i128::MAX` is negative here); every such
    /// pattern fits, except a negative literal for a `u128`.
    pub fn int_fits(&self, v: i128, t: TyId) -> bool {
        let Some(i) = self.types.int(t) else { return false };
        if i.bits == 128 {
            return i.signed || v >= 0;
        }
        if i.signed {
            let lim = 1i128 << (i.bits - 1);
            v >= -lim && v < lim
        } else {
            v >= 0 && v < (1i128 << i.bits)
        }
    }

    /// Wraps an integer to its type's width, sign-extending signed types.
    pub fn wrap_int(&self, v: i128, t: TyId) -> i128 {
        let Some(i) = self.types.int(t) else { return v };
        let m = if i.bits == 128 { v } else { v & ((1i128 << i.bits) - 1) };
        if i.signed && i.bits < 128 && (m >> (i.bits - 1)) & 1 == 1 {
            m - (1i128 << i.bits)
        } else {
            m
        }
    }

    pub fn const_value(&mut self, id: u32) -> R<(Const, TyId)> {
        if let Some(v) = &self.consts[id as usize].value {
            return Ok(v.clone());
        }
        let c = &self.consts[id as usize];
        if c.busy {
            return ty_err(c.span, "this constant's value depends on itself");
        }
        let decl = c.decl;
        let env = Env { module: c.module, names: Vec::new(), self_ty: None };
        self.consts[id as usize].busy = true;
        let exp = match &decl.ty {
            Some(t) => Some(self.resolve_ty(t, &env)?),
            None => None,
        };
        let v = self.const_expr(&decl.value, &env, exp)?;
        if let Some(t) = exp {
            if v.1 != t {
                return ty_err(decl.value.span, &format!("expected `{}`, found `{}`", self.types.show(t), self.types.show(v.1)));
            }
        }
        self.consts[id as usize].busy = false;
        self.consts[id as usize].value = Some(v.clone());
        Ok(v)
    }

    pub fn const_expr(&mut self, e: &ast::Expr, env: &Env, exp: Option<TyId>) -> R<(Const, TyId)> {
        let exp_int = exp.filter(|&t| self.types.is_int(t));
        match &e.kind {
            E::Int(v) => {
                if let Some(t) = exp.filter(|&t| self.types.is_float(t)) {
                    return Ok((Const::Float(*v as f64, t), t));
                }
                let t = exp_int.unwrap_or(types::I64);
                if !self.int_fits(*v as i128, t) {
                    return ty_err(e.span, &format!("{} does not fit in `{}`", v, self.types.show(t)));
                }
                Ok((Const::Int(*v as i128, t), t))
            }
            E::Char(c) => {
                let t = exp_int.unwrap_or(types::U8);
                Ok((Const::Int(*c as i128, t), t))
            }
            E::Float(f) => {
                let t = exp.filter(|&t| self.types.is_float(t)).unwrap_or(types::F64);
                let v = if t == types::F32 { *f as f32 as f64 } else { *f };
                Ok((Const::Float(v, t), t))
            }
            E::Bool(b) => Ok((Const::Bool(*b), types::BOOL)),
            E::Str(s) => Ok((Const::Str(s.clone()), types::STR)),
            E::Unit => Ok((Const::Zst(types::UNIT), types::UNIT)),
            E::Name(n) if n == "null" && exp.map(|t| self.types.is_ptr(t)).unwrap_or(false) && env.get(n).is_none() => {
                let t = exp.unwrap();
                Ok((Const::Null(t), t))
            }
            E::Name(n) => {
                if let Some(v) = env.get(n) {
                    return Ok(match v.clone() {
                        CVal::Int(i) => {
                            let t = exp_int.unwrap_or(types::I64);
                            (Const::Int(i, t), t)
                        }
                        CVal::Bool(b) => (Const::Bool(b), types::BOOL),
                        _ => return ty_err(e.span, &format!("`{}` is not a constant value", n)),
                    });
                }
                match self.lookup(env.module, n) {
                    Some(Sym::Const(c)) => self.const_value(c),
                    _ => ty_err(e.span, &format!("`{}` is not a compile-time constant", n)),
                }
            }
            E::Field(..) => {
                let Some(p) = super::expr_path(e) else { return ty_err(e.span, "not a constant") };
                match self.lookup_path(env.module, &p) {
                    Some((Sym::Const(c), _)) => self.const_value(c),
                    _ => ty_err(e.span, "not a compile-time constant"),
                }
            }
            E::Unary(ast::UnOp::Neg, inner) => match self.const_expr(inner, env, exp)? {
                (Const::Int(v, t), _) => {
                    if !self.types.int(t).map(|i| i.signed).unwrap_or(false) {
                        return ty_err(e.span, "only signed integers can be negated");
                    }
                    Ok((Const::Int(self.wrap_int(-v, t), t), t))
                }
                (Const::Float(v, t), _) => Ok((Const::Float(-v, t), t)),
                _ => ty_err(e.span, "cannot negate this"),
            },
            E::Unary(ast::UnOp::Not, inner) => match self.const_expr(inner, env, exp)? {
                (Const::Int(v, t), _) => Ok((Const::Int(self.wrap_int(!v, t), t), t)),
                (Const::Bool(b), t) => Ok((Const::Bool(!b), t)),
                _ => ty_err(e.span, "cannot apply `!` to this"),
            },
            E::Binary(op, a, b) => {
                let (ca, ta) = self.const_expr(a, env, exp.filter(|_| !op.is_compare()))?;
                let (cb, tb) = self.const_expr(b, env, Some(ta))?;
                if ta != tb && !matches!(op, Op::Shl | Op::Shr) {
                    return ty_err(e.span, &format!("`{}` on `{}` and `{}`", op.text(), self.types.show(ta), self.types.show(tb)));
                }
                self.fold_bin(*op, ca, cb, ta, e.span)
            }
            E::Cast(inner, t) => {
                let to = self.resolve_ty(t, env)?;
                let (c, _) = self.const_expr(inner, env, None)?;
                Ok((self.const_cast(c, to, e.span)?, to))
            }
            E::Call(callee, args) if args.len() == 1 => {
                let name = match &callee.kind {
                    E::Name(n) => n.as_str(),
                    _ => "",
                };
                match name {
                    "size_of" | "align_of" => {
                        let t = self.expr_ty(&args[0], env)?;
                        if matches!(self.types.kind(t), TyKind::Type) {
                            return ty_err(e.span, "types have no size");
                        }
                        let l = self.types.layout(t);
                        let v = if name == "size_of" { l.size } else { l.align };
                        let rt = exp_int.unwrap_or(types::I64);
                        Ok((Const::Int(v as i128, rt), rt))
                    }
                    _ => ty_err(e.span, "this call cannot be evaluated while compiling yet"),
                }
            }
            E::Block(b) if b.stmts.is_empty() && b.tail.is_some() => self.const_expr(b.tail.as_ref().unwrap(), env, exp),
            E::If(c, then, els) => {
                let (cc, _) = self.const_expr(c, env, Some(types::BOOL))?;
                let Const::Bool(cv) = cc else { return ty_err(c.span, "expected a bool") };
                if cv {
                    match &then.tail {
                        Some(t) if then.stmts.is_empty() => self.const_expr(t, env, exp),
                        _ => ty_err(e.span, "not a constant"),
                    }
                } else {
                    match els {
                        Some(x) => self.const_expr(x, env, exp),
                        None => ty_err(e.span, "not a constant"),
                    }
                }
            }
            _ => ty_err(e.span, "this expression cannot be evaluated while compiling yet"),
        }
    }

    fn fold_bin(&mut self, op: Op, a: Const, b: Const, t: TyId, span: crate::diag::Span) -> R<(Const, TyId)> {
        Ok(match (a, b) {
            (Const::Int(x, _), Const::Int(y, _)) => {
                let signed = self.types.int(t).map(|i| i.signed).unwrap_or(true);
                let bits = self.types.int(t).map(|i| i.bits).unwrap_or(64);
                if bits == 128 {
                    return fold_128(op, x, y, signed, t, span);
                }
                let arith = |v: i128, me: &Self| -> R<(Const, TyId)> {
                    if matches!(op, Op::Add | Op::Sub | Op::Mul) && !me.int_fits(v, t) {
                        return ty_err(span, "the result overflows its type");
                    }
                    Ok((Const::Int(me.wrap_int(v, t), t), t))
                };
                match op {
                    Op::Add | Op::AddWrap => arith(x + y, self)?,
                    Op::Sub | Op::SubWrap => arith(x - y, self)?,
                    Op::Mul | Op::MulWrap => arith(x.wrapping_mul(y), self)?,
                    Op::Div | Op::Rem => {
                        if y == 0 {
                            return ty_err(span, "division by zero");
                        }
                        let v = if op == Op::Div { x / y } else { x % y };
                        (Const::Int(self.wrap_int(v, t), t), t)
                    }
                    Op::And => (Const::Int(x & y, t), t),
                    Op::Or => (Const::Int(x | y, t), t),
                    Op::Xor => (Const::Int(self.wrap_int(x ^ y, t), t), t),
                    Op::Shl => (Const::Int(self.wrap_int(x << (y as u32 % bits), t), t), t),
                    Op::Shr => {
                        let ux = if signed { x } else { x & ((1i128 << bits) - 1) };
                        (Const::Int(ux >> (y as u32 % bits), t), t)
                    }
                    Op::Eq => (Const::Bool(x == y), types::BOOL),
                    Op::Ne => (Const::Bool(x != y), types::BOOL),
                    Op::Lt => (Const::Bool(x < y), types::BOOL),
                    Op::Le => (Const::Bool(x <= y), types::BOOL),
                    Op::Gt => (Const::Bool(x > y), types::BOOL),
                    Op::Ge => (Const::Bool(x >= y), types::BOOL),
                    _ => return ty_err(span, "not an integer operator"),
                }
            }
            (Const::Float(x, _), Const::Float(y, _)) => {
                let r = |v: f64| if t == types::F32 { v as f32 as f64 } else { v };
                match op {
                    Op::Add => (Const::Float(r(x + y), t), t),
                    Op::Sub => (Const::Float(r(x - y), t), t),
                    Op::Mul => (Const::Float(r(x * y), t), t),
                    Op::Div => (Const::Float(r(x / y), t), t),
                    Op::Eq => (Const::Bool(x == y), types::BOOL),
                    Op::Ne => (Const::Bool(x != y), types::BOOL),
                    Op::Lt => (Const::Bool(x < y), types::BOOL),
                    Op::Le => (Const::Bool(x <= y), types::BOOL),
                    Op::Gt => (Const::Bool(x > y), types::BOOL),
                    Op::Ge => (Const::Bool(x >= y), types::BOOL),
                    _ => return ty_err(span, "not a float operator"),
                }
            }
            (Const::Bool(x), Const::Bool(y)) => match op {
                Op::LogAnd | Op::And => (Const::Bool(x && y), types::BOOL),
                Op::LogOr | Op::Or => (Const::Bool(x || y), types::BOOL),
                Op::Eq => (Const::Bool(x == y), types::BOOL),
                Op::Ne | Op::Xor => (Const::Bool(x != y), types::BOOL),
                _ => return ty_err(span, "not a bool operator"),
            },
            _ => return ty_err(span, "cannot evaluate this while compiling yet"),
        })
    }

    pub fn const_cast(&mut self, c: Const, to: TyId, span: crate::diag::Span) -> R<Const> {
        Ok(match (c, self.types.kind(to).clone()) {
            (Const::Int(v, _), TyKind::Int(_)) => Const::Int(self.wrap_int(v, to), to),
            (Const::Int(v, from), TyKind::Float(_)) => {
                let unsigned_128 = self.types.int(from).map(|i| i.bits == 128 && !i.signed).unwrap_or(false);
                Const::Float(if unsigned_128 { v as u128 as f64 } else { v as f64 }, to)
            }
            (Const::Float(v, _), TyKind::Float(32)) => Const::Float(v as f32 as f64, to),
            (Const::Float(v, _), TyKind::Float(_)) => Const::Float(v, to),
            (Const::Float(v, _), TyKind::Int(i)) => {
                let x = match (i.signed, i.bits) {
                    (true, 128) => v as i128,
                    (false, 128) => v as u128 as i128,
                    (true, _) => v as i64 as i128,
                    (false, _) => v as u64 as i128,
                };
                Const::Int(self.wrap_int(x, to), to)
            }
            (Const::Bool(b), TyKind::Int(_)) => Const::Int(b as i128, to),
            _ => return ty_err(span, "this conversion cannot be done while compiling"),
        })
    }
}

/// Arithmetic on 128-bit constants, which are bit patterns in an `i128`:
/// at that width, as the program would do it.
fn fold_128(op: Op, x: i128, y: i128, signed: bool, t: TyId, span: crate::diag::Span) -> R<(Const, TyId)> {
    let overflow = || ty_err(span, "the result overflows its type");
    let int = |v: i128| Ok((Const::Int(v, t), t));
    let (ux, uy) = (x as u128, y as u128);
    let n = (y as u32) % 128;
    match op {
        Op::Add if signed => x.checked_add(y).map_or_else(overflow, int),
        Op::Sub if signed => x.checked_sub(y).map_or_else(overflow, int),
        Op::Mul if signed => x.checked_mul(y).map_or_else(overflow, int),
        Op::Add => ux.checked_add(uy).map_or_else(overflow, |v| int(v as i128)),
        Op::Sub => ux.checked_sub(uy).map_or_else(overflow, |v| int(v as i128)),
        Op::Mul => ux.checked_mul(uy).map_or_else(overflow, |v| int(v as i128)),
        Op::AddWrap => int(x.wrapping_add(y)),
        Op::SubWrap => int(x.wrapping_sub(y)),
        Op::MulWrap => int(x.wrapping_mul(y)),
        Op::Div | Op::Rem if y == 0 => ty_err(span, "division by zero"),
        Op::Div if signed => x.checked_div(y).map_or_else(overflow, int),
        Op::Rem if signed => x.checked_rem(y).map_or_else(overflow, int),
        Op::Div => int((ux / uy) as i128),
        Op::Rem => int((ux % uy) as i128),
        Op::And => int(x & y),
        Op::Or => int(x | y),
        Op::Xor => int(x ^ y),
        Op::Shl => int(x << n),
        Op::Shr if signed => int(x >> n),
        Op::Shr => int((ux >> n) as i128),
        Op::Eq => Ok((Const::Bool(x == y), types::BOOL)),
        Op::Ne => Ok((Const::Bool(x != y), types::BOOL)),
        Op::Lt => Ok((Const::Bool(if signed { x < y } else { ux < uy }), types::BOOL)),
        Op::Le => Ok((Const::Bool(if signed { x <= y } else { ux <= uy }), types::BOOL)),
        Op::Gt => Ok((Const::Bool(if signed { x > y } else { ux > uy }), types::BOOL)),
        Op::Ge => Ok((Const::Bool(if signed { x >= y } else { ux >= uy }), types::BOOL)),
        _ => ty_err(span, "not an integer operator"),
    }
}
