// The borrow kernel: exclusivity on MIR.
//
// A borrow (`Ref`, `RefMut`) is a loan of a place, held by a local. Locals
// of view types (borrows, `str`, slices, closures, `#[view]` structs) pass
// their loans on when copied, moved, put in an aggregate or given to a call
// that returns a view. A loan lasts while some local holding it is still
// used later (liveness), so a borrow ends at its last use.
//
// While a mutable loan of a place lasts, nothing else may use the place;
// while a shared loan lasts, nothing may change it. A place may not be
// dropped or go out of scope while borrowed, and a function may return only
// borrows of what its parameters point to.
//
// This pass trusts nothing sema decided about borrows; sema's own checks
// give better messages, this one makes sure.

use crate::diag::{Diag, Span};
use crate::elab::rvalue_operands;
use crate::mir::*;
use crate::types::{TyKind, Types};

#[derive(Clone, Debug)]
struct Loan {
    place: Place,
    mutable: bool,
    span: Span,
}

type Bits = Vec<u64>;

fn set(b: &mut Bits, i: usize) {
    b[i / 64] |= 1 << (i % 64);
}
fn clear(b: &mut Bits, i: usize) {
    b[i / 64] &= !(1 << (i % 64));
}
fn get(b: &Bits, i: usize) -> bool {
    b[i / 64] >> (i % 64) & 1 == 1
}
fn union(a: &mut Bits, b: &Bits) -> bool {
    let mut changed = false;
    for (x, y) in a.iter_mut().zip(b) {
        let n = *x | *y;
        if n != *x {
            *x = n;
            changed = true;
        }
    }
    changed
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Access {
    Read,
    Write,
    /// Going away: a drop or the end of its scope.
    Dead,
}

pub fn run(types: &Types, f: &Function) -> Result<(), Diag> {
    let Some(body) = &f.body else { return Ok(()) };
    let n = body.locals.len();
    let w = n.div_ceil(64).max(1);
    let nb = body.blocks.len();
    let reach = reachable(body);

    // ---- liveness: which locals are used later ----
    let mut live_in: Vec<Bits> = vec![vec![0; w]; nb];
    loop {
        let mut changed = false;
        for b in (0..nb).rev() {
            let mut live = vec![0u64; w];
            for s in succs(&body.blocks[b].term) {
                union(&mut live, &live_in[s as usize]);
            }
            term_live(&body.blocks[b].term, &mut live);
            for s in body.blocks[b].stmts.iter().rev() {
                stmt_live(s, &mut live);
            }
            if union(&mut live_in[b], &live) {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // ---- loans: made at each `Ref`/`RefMut`, followed through views ----
    let mut loans: Vec<Loan> = Vec::new();
    let mut loan_at: std::collections::HashMap<(usize, usize), usize> = std::collections::HashMap::new();
    for (b, blk) in body.blocks.iter().enumerate() {
        for (i, s) in blk.stmts.iter().enumerate() {
            if let Stmt::Assign(_, Rvalue::Ref(p) | Rvalue::RefMut(p), sp) = s {
                if p.proj.iter().any(|x| matches!(x, Proj::Deref)) && root_is_raw(types, body, p) {
                    continue; // through a raw pointer: unsafe code's business
                }
                let mutable = matches!(s, Stmt::Assign(_, Rvalue::RefMut(_), _));
                loan_at.insert((b, i), loans.len());
                loans.push(Loan { place: p.clone(), mutable, span: *sp });
            }
        }
    }
    if loans.is_empty() {
        return Ok(());
    }
    let lw = loans.len().div_ceil(64);
    let is_view: Vec<bool> = body.locals.iter().map(|l| types.is_view(l.ty)).collect();
    // held[block][local] = loans the local holds at the block's start.
    let mut held_in: Vec<Vec<Bits>> = vec![vec![vec![0; lw]; n]; nb];
    let mut seen = vec![false; nb];
    seen[0] = true;
    loop {
        let mut changed = false;
        for b in 0..nb {
            if !seen[b] {
                continue;
            }
            let mut held = held_in[b].clone();
            for (i, s) in body.blocks[b].stmts.iter().enumerate() {
                stmt_loans(s, &mut held, &is_view, loan_at.get(&(b, i)).copied(), lw);
            }
            term_loans(&body.blocks[b].term, &mut held, &is_view, types, body, lw);
            for s in succs(&body.blocks[b].term) {
                let s = s as usize;
                if !seen[s] {
                    seen[s] = true;
                    changed = true;
                }
                for l in 0..n {
                    if union(&mut held_in[s][l], &held[l]) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // ---- checking ----
    for b in 0..nb {
        if !reach[b] {
            continue;
        }
        // Liveness after each statement of the block.
        let blk = &body.blocks[b];
        let mut after: Vec<Bits> = vec![vec![0; w]; blk.stmts.len() + 1];
        let mut live = vec![0u64; w];
        for s in succs(&blk.term) {
            union(&mut live, &live_in[s as usize]);
        }
        after[blk.stmts.len()] = live.clone();
        term_live(&blk.term, &mut live);
        for i in (0..blk.stmts.len()).rev() {
            after[i] = live.clone();
            stmt_live(&blk.stmts[i], &mut live);
        }
        let mut held = held_in[b].clone();
        for (i, s) in blk.stmts.iter().enumerate() {
            let active = active_loans(&held, &after[i], n, lw);
            check_stmt(types, body, s, &active, &held, &loans)?;
            stmt_loans(s, &mut held, &is_view, loan_at.get(&(b, i)).copied(), lw);
        }
        let active = active_loans(&held, &after[blk.stmts.len()], n, lw);
        check_term(types, body, &blk.term, &active, &held, &loans, f)?;
    }
    Ok(())
}

fn root_is_raw(types: &Types, body: &Body, p: &Place) -> bool {
    // A place reached through a raw pointer somewhere along its path.
    let mut t = body.locals[p.local as usize].ty;
    let mut variant = None;
    for pr in &p.proj {
        match pr {
            Proj::Deref => {
                if matches!(types.kind(t), TyKind::Ptr(_)) {
                    return true;
                }
                t = types.pointee(t).unwrap();
            }
            Proj::Variant(v) => variant = Some(*v),
            Proj::Field(i) => {
                t = if let Some(v) = variant.take() {
                    types.variants(t).unwrap()[v as usize].fields[*i as usize]
                } else {
                    match types.kind(t) {
                        TyKind::Slice(_) | TyKind::Str | TyKind::Closure(_) => return true,
                        _ => types.field_tys(t)[*i as usize],
                    }
                }
            }
            Proj::Index(_) => {
                if let TyKind::Array(e, _) = types.kind(t) {
                    t = *e;
                }
            }
        }
    }
    false
}

fn reachable(body: &Body) -> Vec<bool> {
    let mut r = vec![false; body.blocks.len()];
    let mut stack = vec![0usize];
    while let Some(b) = stack.pop() {
        if r[b] {
            continue;
        }
        r[b] = true;
        for s in succs(&body.blocks[b].term) {
            stack.push(s as usize);
        }
    }
    r
}

pub fn succs(t: &Term) -> Vec<BlockId> {
    match t {
        Term::Goto(b) => vec![*b],
        Term::Switch { targets, otherwise, .. } => {
            let mut v: Vec<BlockId> = targets.iter().map(|x| x.1).collect();
            v.push(*otherwise);
            v
        }
        Term::Call { next, .. } | Term::Assert { next, .. } => vec![*next],
        _ => vec![],
    }
}

fn place_uses(p: &Place, live: &mut Bits) {
    set(live, p.local as usize);
    for x in &p.proj {
        if let Proj::Index(l) = x {
            set(live, *l as usize);
        }
    }
}

fn op_uses(o: &Operand, live: &mut Bits) {
    if let Operand::Copy(p) | Operand::Move(p) = o {
        place_uses(p, live);
    }
}

fn stmt_live(s: &Stmt, live: &mut Bits) {
    match s {
        Stmt::Assign(p, r, _) => {
            if p.proj.is_empty() {
                clear(live, p.local as usize);
            } else {
                place_uses(p, live);
            }
            for o in rvalue_operands(r) {
                op_uses(o, live);
            }
            if let Rvalue::Ref(q) | Rvalue::RefMut(q) | Rvalue::Addr(q) | Rvalue::Discriminant(q) = r {
                place_uses(q, live);
            }
        }
        Stmt::Drop(p, _) => place_uses(p, live),
        _ => {}
    }
}

fn term_live(t: &Term, live: &mut Bits) {
    match t {
        Term::Switch { discr, .. } => op_uses(discr, live),
        Term::Return => set(live, RET as usize),
        Term::Call { callee, args, dest, .. } => {
            if dest.proj.is_empty() {
                clear(live, dest.local as usize);
            } else {
                place_uses(dest, live);
            }
            for a in args {
                op_uses(a, live);
            }
            if let Callee::Ptr(o) | Callee::Closure(o) = callee {
                op_uses(o, live);
            }
        }
        Term::Assert { cond, .. } => op_uses(cond, live),
        _ => {}
    }
}

/// The loans an operand carries (those of the local it reads, if a view).
fn op_loans(o: &Operand, held: &[Bits], is_view: &[bool], lw: usize) -> Bits {
    match o {
        Operand::Copy(p) | Operand::Move(p) if is_view[p.local as usize] || p.proj.iter().any(|x| matches!(x, Proj::Deref)) => {
            held[p.local as usize].clone()
        }
        _ => vec![0; lw],
    }
}

fn stmt_loans(s: &Stmt, held: &mut [Bits], is_view: &[bool], new: Option<usize>, lw: usize) {
    match s {
        Stmt::Assign(p, r, _) => {
            let mut gained = vec![0u64; lw];
            for o in rvalue_operands(r) {
                union(&mut gained, &op_loans(o, held, is_view, lw));
            }
            if let Rvalue::Ref(q) | Rvalue::RefMut(q) = r {
                // A reborrow through a borrow, or a borrow of a view (a
                // closure's environment), keeps the loans it holds too.
                if q.proj.first() == Some(&Proj::Deref) || is_view[q.local as usize] {
                    let h = held[q.local as usize].clone();
                    union(&mut gained, &h);
                }
            }
            if let Some(l) = new {
                set(&mut gained, l);
            }
            for o in rvalue_operands(r) {
                if let Operand::Move(m) = o {
                    if m.proj.is_empty() {
                        held[m.local as usize] = vec![0; lw];
                    }
                }
            }
            let d = p.local as usize;
            if !is_view[d] && p.proj.first() != Some(&Proj::Deref) {
                return;
            }
            if p.proj.is_empty() {
                held[d] = gained;
            } else {
                union(&mut held[d], &gained);
            }
        }
        Stmt::StorageDead(l) | Stmt::Forget(l) => held[*l as usize] = vec![0; lw],
        _ => {}
    }
}

fn term_loans(t: &Term, held: &mut [Bits], is_view: &[bool], types: &Types, body: &Body, lw: usize) {
    if let Term::Call { args, dest, .. } = t {
        let mut all = vec![0u64; lw];
        for a in args {
            union(&mut all, &op_loans(a, held, is_view, lw));
        }
        // What a call is given can end up in its `inout` arguments that
        // are views (`v.push(s.as_str())` with `v: Vec(str)`).
        for a in args {
            if let Operand::Copy(p) | Operand::Move(p) = a {
                if p.proj.is_empty() {
                    if let TyKind::RefMut(inner) = types.kind(body.locals[p.local as usize].ty) {
                        if types.is_view(*inner) {
                            // The loans go to whatever the borrow points to.
                            let targets: Vec<usize> = (0..held.len()).filter(|&l| intersects(&held[p.local as usize], &held[l]) && l != p.local as usize).collect();
                            for l in targets {
                                union(&mut held[l], &all);
                            }
                        }
                    }
                }
            }
        }
        for a in args {
            if let Operand::Move(m) = a {
                if m.proj.is_empty() {
                    held[m.local as usize] = vec![0; lw];
                }
            }
        }
        let d = dest.local as usize;
        if is_view[d] {
            if dest.proj.is_empty() {
                held[d] = all;
            } else {
                union(&mut held[d], &all);
            }
        }
    }
}

fn intersects(a: &Bits, b: &Bits) -> bool {
    a.iter().zip(b).any(|(x, y)| x & y != 0)
}

/// Loans held by some local that is still used later.
fn active_loans(held: &[Bits], live_after: &Bits, n: usize, lw: usize) -> Bits {
    let mut a = vec![0u64; lw];
    for (l, h) in held.iter().enumerate().take(n) {
        if get(live_after, l) {
            union(&mut a, h);
        }
    }
    a
}

/// Whether two places may share memory.
fn overlap(a: &Place, b: &Place) -> bool {
    if a.local != b.local {
        return false;
    }
    for (x, y) in a.proj.iter().zip(&b.proj) {
        match (x, y) {
            (Proj::Field(i), Proj::Field(j)) if i != j => return false,
            (Proj::Variant(i), Proj::Variant(j)) if i != j => return false,
            _ => {}
        }
    }
    true
}

fn name(body: &Body, p: &Place) -> String {
    match &body.locals[p.local as usize].name {
        Some(n) => format!("`{}`", n),
        None => "a value".into(),
    }
}

fn conflict(types: &Types, body: &Body, q: &Place, access: Access, span: Span, active: &Bits, held: &[Bits], loans: &[Loan]) -> Result<(), Diag> {
    let _ = types;
    let own = &held[q.local as usize];
    for (i, l) in loans.iter().enumerate() {
        if !get(active, i) || get(own, i) {
            continue;
        }
        if !overlap(&l.place, q) {
            continue;
        }
        // A borrow through a pointer does not borrow the pointer's own
        // storage, which may go away (the pointee's loans live on in the
        // reborrow).
        if access == Access::Dead && l.place.proj.first() == Some(&Proj::Deref) && q.proj.is_empty() {
            continue;
        }
        let bad = l.mutable || access != Access::Read;
        if !bad {
            continue;
        }
        let what = name(body, q);
        let msg = match (access, l.mutable) {
            (Access::Dead, _) => format!("{} goes away here while it is still borrowed", what),
            (_, true) => format!("{} is used here while it is borrowed mutably", what),
            (_, false) => format!("{} is changed here while it is borrowed", what),
        };
        return Err(Diag::new(span, &msg).note(Some(l.span), "the borrow starts here, and is used later"));
    }
    Ok(())
}

fn op_access(types: &Types, body: &Body, o: &Operand, span: Span, active: &Bits, held: &[Bits], loans: &[Loan]) -> Result<(), Diag> {
    match o {
        Operand::Copy(p) => conflict(types, body, p, Access::Read, span, active, held, loans),
        Operand::Move(p) => {
            if is_ref_local(types, body, p) {
                return Ok(());
            }
            conflict(types, body, p, Access::Write, span, active, held, loans)
        }
        Operand::Const(_) => Ok(()),
    }
}

fn is_ref_local(types: &Types, body: &Body, p: &Place) -> bool {
    p.proj.is_empty() && types.is_ref(body.locals[p.local as usize].ty)
}

fn check_stmt(types: &Types, body: &Body, s: &Stmt, active: &Bits, held: &[Bits], loans: &[Loan]) -> Result<(), Diag> {
    match s {
        Stmt::Assign(p, r, span) => {
            for o in rvalue_operands(r) {
                op_access(types, body, o, *span, active, held, loans)?;
            }
            match r {
                Rvalue::Ref(q) | Rvalue::Discriminant(q) => conflict(types, body, q, Access::Read, *span, active, held, loans)?,
                Rvalue::RefMut(q) => conflict(types, body, q, Access::Write, *span, active, held, loans)?,
                _ => {}
            }
            // Writing a place: not through the loans the written local holds.
            if !(p.proj.is_empty() && types.is_view(body.locals[p.local as usize].ty) && body.locals[p.local as usize].kind == LocalKind::Temp) {
                conflict(types, body, p, Access::Write, *span, active, held, loans)?;
            }
        }
        Stmt::Drop(p, span) => conflict(types, body, p, Access::Dead, *span, active, held, loans)?,
        Stmt::StorageDead(l) => {
            let p = Place::local(*l);
            let span = body.locals[*l as usize].span;
            conflict(types, body, &p, Access::Dead, span, active, held, loans)?;
        }
        _ => {}
    }
    Ok(())
}

fn check_term(types: &Types, body: &Body, t: &Term, active: &Bits, held: &[Bits], loans: &[Loan], f: &Function) -> Result<(), Diag> {
    match t {
        Term::Call { args, dest, span, callee, .. } => {
            for a in args {
                op_access(types, body, a, *span, active, held, loans)?;
            }
            if let Callee::Ptr(o) | Callee::Closure(o) = callee {
                op_access(types, body, o, *span, active, held, loans)?;
            }
            let _ = dest;
        }
        Term::Switch { discr, .. } => op_access(types, body, discr, f.span, active, held, loans)?,
        Term::Assert { cond, span, .. } => op_access(types, body, cond, *span, active, held, loans)?,
        Term::Return => {
            // What the result borrows must outlive the call: it is reached
            // through a parameter.
            for (i, l) in loans.iter().enumerate() {
                if !get(&held[RET as usize], i) {
                    continue;
                }
                let root = &body.locals[l.place.local as usize];
                let through_param = root.kind == LocalKind::Arg && l.place.proj.first() == Some(&Proj::Deref);
                // A reborrow through a borrow (`&(*r)`, `r` from a call that
                // returns `ref T`) holds the loans of `r` too, and those are
                // checked here as well.
                let reborrow = l.place.proj.first() == Some(&Proj::Deref) && types.is_ref(root.ty);
                if !through_param && !reborrow && !root_is_raw(types, body, &l.place) {
                    return Err(Diag::new(l.span, &format!("the result borrows {}, which goes away when the function returns", name(body, &l.place))));
                }
            }
        }
        _ => {}
    }
    Ok(())
}
