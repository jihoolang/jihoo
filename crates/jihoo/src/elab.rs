// Initialization: which locals hold a value at each point. Uses of a moved
// value are errors; drops of moved values are removed; a value moved on
// only some paths gets a flag, and its drop checks the flag.

use crate::diag::{Diag, Span};
use crate::mir::*;
use crate::types::{self, Types};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum St {
    Uninit,
    Init,
    /// Init on some paths, not on others.
    Maybe,
    /// Some parts moved out (only temporaries, which are then forgotten).
    Partial,
    /// Not reached yet.
    Bottom,
}

fn join(a: St, b: St) -> St {
    match (a, b) {
        (St::Bottom, x) | (x, St::Bottom) => x,
        (x, y) if x == y => x,
        (St::Partial, _) | (_, St::Partial) => St::Partial,
        _ => St::Maybe,
    }
}

pub fn run(types: &mut Types, f: &mut Function) -> Result<(), Diag> {
    let Some(body) = f.body.as_mut() else { return Ok(()) };
    let n = body.locals.len();
    let nb = body.blocks.len();
    let mut entry: Vec<Vec<St>> = vec![vec![St::Bottom; n]; nb];
    let mut init = vec![St::Uninit; n];
    for (i, l) in body.locals.iter().enumerate() {
        if l.kind == LocalKind::Arg {
            init[i] = St::Init;
        }
    }
    entry[0] = init;
    // Fixpoint over blocks.
    let mut work: Vec<usize> = vec![0];
    let mut on = vec![false; nb];
    on[0] = true;
    while let Some(b) = work.pop() {
        on[b] = false;
        let mut st = entry[b].clone();
        for s in &body.blocks[b].stmts {
            transfer(&mut st, s, None, body, types)?;
        }
        let out = term_transfer(&mut st, &body.blocks[b].term, body, None)?;
        for (succ, s) in out {
            let mut changed = false;
            for i in 0..n {
                let j = join(entry[succ][i], s[i]);
                if j != entry[succ][i] {
                    entry[succ][i] = j;
                    changed = true;
                }
            }
            if changed && !on[succ] {
                on[succ] = true;
                work.push(succ);
            }
        }
    }
    // Check uses, and find drops to remove or guard.
    let mut flags: Vec<Option<Local>> = vec![None; n];
    let mut edits: Vec<(usize, usize, St)> = Vec::new();
    for (b, start) in entry.iter().enumerate() {
        if start.iter().all(|s| *s == St::Bottom) && b != 0 {
            continue; // unreachable
        }
        let mut st = start.clone();
        for (si, s) in body.blocks[b].stmts.iter().enumerate() {
            if let Stmt::Drop(p, _) = s {
                if p.proj.is_empty() {
                    edits.push((b, si, st[p.local as usize]));
                }
            }
            transfer(&mut st, s, Some(()), body, types)?;
        }
        term_transfer(&mut st, &body.blocks[b].term, body, Some(()))?;
    }
    for &(b, si, s) in &edits {
        if s == St::Maybe {
            let Stmt::Drop(p, _) = &body.blocks[b].stmts[si] else { unreachable!() };
            let l = p.local as usize;
            if flags[l].is_none() {
                let sp = body.locals[l].span;
                body.locals.push(LocalDecl { ty: types::BOOL, name: None, span: sp, mutable: true, kind: LocalKind::Temp });
                flags[l] = Some((body.locals.len() - 1) as Local);
            }
        }
    }
    // Remove drops of values that are gone; guard the maybe ones.
    let mut guarded: Vec<(usize, usize)> = Vec::new();
    for &(b, si, s) in &edits {
        match s {
            St::Uninit | St::Bottom => body.blocks[b].stmts[si] = Stmt::Nop,
            St::Maybe => guarded.push((b, si)),
            St::Partial => {
                let span = match &body.blocks[b].stmts[si] {
                    Stmt::Drop(_, sp) => *sp,
                    _ => Span::default(),
                };
                return Err(Diag::new(span, "internal error: a value with parts moved out is dropped whole"));
            }
            St::Init => {}
        }
    }
    if flags.iter().any(|f| f.is_some()) {
        insert_flags(body, &flags);
        // Split blocks at guarded drops, last first so indices stay valid.
        guarded.sort();
        for &(b, si) in guarded.iter().rev() {
            let Stmt::Drop(p, sp) = body.blocks[b].stmts[si].clone() else { continue };
            let flag = flags[p.local as usize].unwrap();
            let rest: Vec<Stmt> = body.blocks[b].stmts.split_off(si + 1);
            body.blocks[b].stmts.pop();
            let term = std::mem::replace(&mut body.blocks[b].term, Term::Pending);
            let cont = body.blocks.len() as BlockId;
            body.blocks.push(Block { stmts: rest, term });
            let drop_b = body.blocks.len() as BlockId;
            body.blocks.push(Block { stmts: vec![Stmt::Drop(p.clone(), sp), Stmt::Assign(Place::local(flag), Rvalue::Use(Operand::Const(Const::Bool(false))), sp)], term: Term::Goto(cont) });
            body.blocks[b].term = Term::Switch { discr: Operand::Copy(Place::local(flag)), targets: vec![(0, cont)], otherwise: drop_b };
        }
    }
    Ok(())
}

/// Sets each flag where its local gets or loses its value.
fn insert_flags(body: &mut Body, flags: &[Option<Local>]) {
    let set = |f: Local, v: bool| Stmt::Assign(Place::local(f), Rvalue::Use(Operand::Const(Const::Bool(v))), Span::default());
    let mut call_inits: Vec<(BlockId, Local)> = Vec::new();
    for b in 0..body.blocks.len() {
        let old = std::mem::take(&mut body.blocks[b].stmts);
        let mut new = Vec::with_capacity(old.len());
        for s in old {
            let mut after: Vec<Stmt> = Vec::new();
            match &s {
                Stmt::Assign(p, r, _) => {
                    for o in rvalue_operands(r) {
                        if let Operand::Move(mp) = o {
                            if let Some(f) = flags[mp.local as usize] {
                                after.push(set(f, false));
                            }
                        }
                    }
                    if p.proj.is_empty() {
                        if let Some(f) = flags[p.local as usize] {
                            after.push(set(f, true));
                        }
                    }
                }
                Stmt::Forget(l) => {
                    if let Some(f) = flags[*l as usize] {
                        after.push(set(f, false));
                    }
                }
                _ => {}
            }
            new.push(s);
            new.extend(after);
        }
        body.blocks[b].stmts = new;
        if let Term::Call { args, dest, next, .. } = body.blocks[b].term.clone() {
            let mut pre = Vec::new();
            for o in &args {
                if let Operand::Move(mp) = o {
                    if let Some(f) = flags[mp.local as usize] {
                        pre.push(set(f, false));
                    }
                }
            }
            // A moved argument's flag clears before the call.
            body.blocks[b].stmts.extend(pre);
            if dest.proj.is_empty() {
                if let Some(f) = flags[dest.local as usize] {
                    call_inits.push((next, f));
                }
            }
        }
    }
    for (b, f) in call_inits {
        body.blocks[b as usize].stmts.insert(0, set(f, true));
    }
    // Every flag starts false.
    let mut pre: Vec<Stmt> = flags.iter().flatten().map(|&f| set(f, false)).collect();
    pre.extend(std::mem::take(&mut body.blocks[0].stmts));
    body.blocks[0].stmts = pre;
}

pub fn rvalue_operands(r: &Rvalue) -> Vec<&Operand> {
    match r {
        Rvalue::Use(o) | Rvalue::Un(_, o) | Rvalue::Cast(o, _, _) | Rvalue::Repeat(o, _) => vec![o],
        Rvalue::Bin(_, a, b) | Rvalue::Offset(a, b) => vec![a, b],
        Rvalue::Aggregate(_, os) => os.iter().collect(),
        Rvalue::Ref(_) | Rvalue::RefMut(_) | Rvalue::Addr(_) | Rvalue::Discriminant(_) => vec![],
    }
}

fn local_name(body: &Body, l: Local) -> String {
    match &body.locals[l as usize].name {
        Some(n) => format!("`{}`", n),
        None => "a value".to_string(),
    }
}

/// Checks that a place's root holds a value.
fn use_place(st: &[St], p: &Place, body: &Body, span: Span, check: bool) -> Result<(), Diag> {
    if !check {
        return Ok(());
    }
    let s = st[p.local as usize];
    match s {
        St::Init => Ok(()),
        St::Partial if !p.proj.is_empty() && !matches!(p.proj[0], Proj::Deref) => Ok(()),
        St::Maybe => Err(Diag::new(span, &format!("{} is used here, but it may have been moved away before", local_name(body, p.local)))),
        St::Uninit | St::Partial => Err(Diag::new(span, &format!("{} is used here after it was moved away", local_name(body, p.local))).note(None, &format!("local _{}", p.local))),
        St::Bottom => Ok(()),
    }
}

fn index_uses(p: &Place) -> Vec<Local> {
    p.proj.iter().filter_map(|x| if let Proj::Index(l) = x { Some(*l) } else { None }).collect()
}

fn op_transfer(st: &mut [St], o: &Operand, body: &Body, span: Span, check: bool) -> Result<(), Diag> {
    match o {
        Operand::Copy(p) => {
            use_place(st, p, body, span, check)?;
            for l in index_uses(p) {
                use_place(st, &Place::local(l), body, span, check)?;
            }
        }
        Operand::Move(p) => {
            use_place(st, p, body, span, check)?;
            if p.proj.is_empty() {
                st[p.local as usize] = St::Uninit;
            } else if !matches!(p.proj[0], Proj::Deref) {
                st[p.local as usize] = St::Partial;
            }
        }
        Operand::Const(_) => {}
    }
    Ok(())
}

fn transfer(st: &mut [St], s: &Stmt, check: Option<()>, body: &Body, _types: &Types) -> Result<(), Diag> {
    let check = check.is_some();
    match s {
        Stmt::Assign(p, r, span) => {
            for o in rvalue_operands(r) {
                op_transfer(st, o, body, *span, check)?;
            }
            if let Rvalue::Ref(q) | Rvalue::RefMut(q) | Rvalue::Addr(q) | Rvalue::Discriminant(q) = r {
                use_place(st, q, body, *span, check)?;
            }
            if p.proj.is_empty() {
                st[p.local as usize] = St::Init;
            } else {
                // Writing a part: the whole must hold a value (or the write
                // goes through a borrow).
                use_place(st, &Place { local: p.local, proj: vec![] }, body, *span, check && !matches!(p.proj[0], Proj::Deref) && st[p.local as usize] != St::Partial)?;
                if matches!(p.proj[0], Proj::Deref) {
                    use_place(st, &Place::local(p.local), body, *span, check)?;
                }
            }
        }
        Stmt::Drop(p, span) => {
            if !p.proj.is_empty() {
                use_place(st, p, body, *span, check && !matches!(st[p.local as usize], St::Partial))?;
            }
        }
        Stmt::Forget(l) | Stmt::StorageDead(l) | Stmt::StorageLive(l) => st[*l as usize] = St::Uninit,
        Stmt::Nop => {}
    }
    Ok(())
}

fn term_transfer(st: &mut [St], t: &Term, body: &Body, check: Option<()>) -> Result<Vec<(usize, Vec<St>)>, Diag> {
    let c = check.is_some();
    Ok(match t {
        Term::Goto(b) => vec![(*b as usize, st.to_vec())],
        Term::Switch { discr, targets, otherwise } => {
            op_transfer(st, discr, body, Span::default(), c)?;
            let mut v: Vec<(usize, Vec<St>)> = targets.iter().map(|(_, b)| (*b as usize, st.to_vec())).collect();
            v.push((*otherwise as usize, st.to_vec()));
            v
        }
        Term::Return => {
            if c && body.locals[0].ty != types::NEVER {
                // The result must be set (unless the function returns ()).
            }
            vec![]
        }
        Term::Unreachable | Term::Pending => vec![],
        Term::Call { args, dest, next, span, .. } => {
            for o in args {
                op_transfer(st, o, body, *span, c)?;
            }
            if let Term::Call { callee: Callee::Closure(o) | Callee::Ptr(o), .. } = t {
                op_transfer(st, o, body, *span, c)?;
            }
            if dest.proj.is_empty() {
                st[dest.local as usize] = St::Init;
            }
            vec![(*next as usize, st.to_vec())]
        }
        Term::Assert { cond, next, span, .. } => {
            op_transfer(st, cond, body, *span, c)?;
            vec![(*next as usize, st.to_vec())]
        }
    })
}
