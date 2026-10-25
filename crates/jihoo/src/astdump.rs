// The syntax tree as S-expressions, with every span, for `jihoo emit-ast`.
// The compiler written in jihoo prints the same (compiler/astdump.jh), so
// the two parsers can be compared.

use crate::ast::*;
use crate::diag::Span;

pub fn module(m: &Module) -> String {
    let mut d = Dump { out: String::new() };
    d.s("(module [");
    d.words(&m.attrs);
    d.s("]");
    for it in &m.items {
        d.s("\n ");
        d.item(it);
    }
    d.s(")\n");
    d.out
}

struct Dump {
    out: String,
}

impl Dump {
    fn s(&mut self, s: &str) {
        self.out.push_str(s);
    }

    fn open(&mut self, tag: &str, sp: Span) {
        self.out.push_str(&format!("({} {}:{}", tag, sp.lo, sp.hi));
    }

    fn words(&mut self, ws: &[String]) {
        for (i, w) in ws.iter().enumerate() {
            if i > 0 {
                self.s(" ");
            }
            self.s(w);
        }
    }

    fn bytes(&mut self, b: &[u8]) {
        self.s(" \"");
        for c in b {
            self.out.push_str(&format!("{:02x}", c));
        }
        self.s("\"");
    }

    fn mode(&mut self, m: Mode) {
        self.s(match m {
            Mode::Let => " let",
            Mode::Inout => " inout",
            Mode::Sink => " sink",
            Mode::Comptime => " comptime",
        });
    }

    fn opt_ty(&mut self, t: &Option<Ty>) {
        match t {
            Some(t) => {
                self.s(" ");
                self.ty(t);
            }
            None => self.s(" _"),
        }
    }

    fn opt_expr(&mut self, e: Option<&Expr>) {
        match e {
            Some(e) => {
                self.s(" ");
                self.expr(e);
            }
            None => self.s(" _"),
        }
    }

    fn tys(&mut self, ts: &[Ty]) {
        self.s(" [");
        for (i, t) in ts.iter().enumerate() {
            if i > 0 {
                self.s(" ");
            }
            self.ty(t);
        }
        self.s("]");
    }

    fn exprs(&mut self, es: &[Expr]) {
        self.s(" [");
        for (i, e) in es.iter().enumerate() {
            if i > 0 {
                self.s(" ");
            }
            self.expr(e);
        }
        self.s("]");
    }

    fn pats(&mut self, ps: &[Pat]) {
        self.s(" [");
        for (i, p) in ps.iter().enumerate() {
            if i > 0 {
                self.s(" ");
            }
            self.pat(p);
        }
        self.s("]");
    }

    fn params(&mut self, ps: &[Param]) {
        self.s(" [");
        for (i, p) in ps.iter().enumerate() {
            if i > 0 {
                self.s(" ");
            }
            self.open("param", p.span);
            self.s(" ");
            self.s(&p.name);
            self.mode(p.mode);
            self.opt_ty(&p.ty);
            self.tys(&p.bounds);
            self.s(")");
        }
        self.s("]");
    }

    fn items(&mut self, items: &[Item]) {
        self.s(" [");
        for (i, it) in items.iter().enumerate() {
            if i > 0 {
                self.s(" ");
            }
            self.item(it);
        }
        self.s("]");
    }

    fn item(&mut self, it: &Item) {
        self.open("item", it.span);
        self.s(if it.public { " pub [" } else { " priv [" });
        for (i, a) in it.attrs.iter().enumerate() {
            if i > 0 {
                self.s(" ");
            }
            self.open("attr", a.span);
            self.s(" ");
            self.s(&a.name);
            self.s(" [");
            self.words(&a.args);
            self.s("])");
        }
        self.s("] ");
        match &it.kind {
            ItemKind::Import(im) => {
                self.s("(import [");
                self.words(&im.path);
                self.s("] ");
                self.s(im.alias.as_deref().unwrap_or("_"));
                self.s(")");
            }
            ItemKind::Fn(f) => {
                self.s("(fn ");
                self.s(&f.name);
                self.out.push_str(&format!(" {}:{}", f.name_span.lo, f.name_span.hi));
                self.s(match f.kind {
                    FnKind::Normal => " normal",
                    FnKind::Extern => " extern",
                    FnKind::Export => " export",
                });
                self.s(if f.is_unsafe { " unsafe" } else { " safe" });
                self.s(if f.variadic { " variadic" } else { " fixed" });
                self.params(&f.params);
                self.s(match f.ret_mode {
                    RetMode::Value => " value",
                    RetMode::Ref => " ref",
                    RetMode::Inout => " inout",
                });
                self.opt_ty(&f.ret);
                match &f.body {
                    Some(b) => {
                        self.s(" ");
                        self.block(b);
                    }
                    None => self.s(" _"),
                }
                self.s(")");
            }
            ItemKind::Struct(s) => {
                self.s("(struct ");
                self.s(&s.name);
                self.params(&s.params);
                self.s(" [");
                for (i, f) in s.fields.iter().enumerate() {
                    if i > 0 {
                        self.s(" ");
                    }
                    self.open("field", f.span);
                    self.s(" ");
                    self.s(&f.name);
                    self.s(if f.public { " pub " } else { " priv " });
                    self.ty(&f.ty);
                    self.s(")");
                }
                self.s("])");
            }
            ItemKind::Enum(e) => {
                self.s("(enum ");
                self.s(&e.name);
                self.params(&e.params);
                self.s(" [");
                for (i, v) in e.variants.iter().enumerate() {
                    if i > 0 {
                        self.s(" ");
                    }
                    self.open("variant", v.span);
                    self.s(" ");
                    self.s(&v.name);
                    self.tys(&v.fields);
                    self.s(")");
                }
                self.s("])");
            }
            ItemKind::Impl(im) => {
                self.s("(impl");
                self.params(&im.params);
                self.opt_ty(&im.trait_);
                self.s(" ");
                self.ty(&im.self_ty);
                self.items(&im.items);
                self.s(")");
            }
            ItemKind::Trait(t) => {
                self.s("(trait ");
                self.s(&t.name);
                self.params(&t.params);
                self.tys(&t.supertraits);
                self.items(&t.items);
                self.s(")");
            }
            ItemKind::Const(c) | ItemKind::Static(c) => {
                self.s(if matches!(it.kind, ItemKind::Const(_)) { "(const " } else { "(static " });
                self.s(&c.name);
                self.opt_ty(&c.ty);
                self.s(" ");
                self.expr(&c.value);
                self.s(")");
            }
            ItemKind::TypeAlias(name, t) => {
                self.s("(type ");
                self.s(name);
                self.opt_ty(t);
                self.s(")");
            }
        }
        self.s(")");
    }

    fn fn_ty(&mut self, ps: &[(Mode, Ty)], r: &Option<Box<Ty>>) {
        self.s(" [");
        for (i, (m, t)) in ps.iter().enumerate() {
            if i > 0 {
                self.s(" ");
            }
            self.s("(");
            self.mode(*m);
            self.s(" ");
            self.ty(t);
            self.s(")");
        }
        self.s("]");
        match r {
            Some(t) => {
                self.s(" ");
                self.ty(t);
            }
            None => self.s(" _"),
        }
    }

    fn ty(&mut self, t: &Ty) {
        match &t.kind {
            TyKind::Path(p, args) => {
                self.open("path", t.span);
                self.s(" [");
                self.words(p);
                self.s("]");
                match args {
                    Some(a) => self.exprs(a),
                    None => self.s(" _"),
                }
            }
            TyKind::Ptr(i) => {
                self.open("ptr", t.span);
                self.s(" ");
                self.ty(i);
            }
            TyKind::Ref(i, m) => {
                self.open(if *m { "inout" } else { "ref" }, t.span);
                self.s(" ");
                self.ty(i);
            }
            TyKind::Array(i, n) => {
                self.open("array", t.span);
                self.s(" ");
                self.ty(i);
                self.s(" ");
                self.expr(n);
            }
            TyKind::Slice(i) => {
                self.open("slice", t.span);
                self.s(" ");
                self.ty(i);
            }
            TyKind::Tuple(ts) => {
                self.open("tuple", t.span);
                self.tys(ts);
            }
            TyKind::Fn(ps, r) => {
                self.open("fn", t.span);
                self.fn_ty(ps, r);
            }
            TyKind::FnPtr(ps, r) => {
                self.open("fnptr", t.span);
                self.fn_ty(ps, r);
            }
        }
        self.s(")");
    }

    fn block(&mut self, b: &Block) {
        self.open("block", b.span);
        self.s(" [");
        for (i, st) in b.stmts.iter().enumerate() {
            if i > 0 {
                self.s(" ");
            }
            self.stmt(st);
        }
        self.s("]");
        self.opt_expr(b.tail.as_deref());
        self.s(")");
    }

    fn stmt(&mut self, st: &Stmt) {
        match &st.kind {
            StmtKind::Let { kind, pat, ty, value } => {
                self.open("let", st.span);
                self.s(match kind {
                    LetKind::Let => " let ",
                    LetKind::Var => " var ",
                    LetKind::Inout => " inout ",
                });
                self.pat(pat);
                self.opt_ty(ty);
                self.s(" ");
                self.expr(value);
            }
            StmtKind::Assign(l, r) => {
                self.open("assign", st.span);
                self.s(" ");
                self.expr(l);
                self.s(" ");
                self.expr(r);
            }
            StmtKind::OpAssign(op, l, r) => {
                self.open("opassign", st.span);
                self.s(" ");
                self.s(op.text());
                self.s(" ");
                self.expr(l);
                self.s(" ");
                self.expr(r);
            }
            StmtKind::Expr(e) => {
                self.open("expr", st.span);
                self.s(" ");
                self.expr(e);
            }
        }
        self.s(")");
    }

    fn expr(&mut self, e: &Expr) {
        let sp = e.span;
        match &e.kind {
            ExprKind::Int(n) => {
                self.open("int", sp);
                self.out.push_str(&format!(" {}", n));
            }
            ExprKind::Float(f) => {
                self.open("float", sp);
                self.out.push_str(&format!(" {}", f.to_bits()));
            }
            ExprKind::Str(b) => {
                self.open("str", sp);
                self.bytes(b);
            }
            ExprKind::Char(c) => {
                self.open("char", sp);
                self.out.push_str(&format!(" {}", c));
            }
            ExprKind::Bool(b) => {
                self.open("bool", sp);
                self.s(if *b { " true" } else { " false" });
            }
            ExprKind::Unit => self.open("unit", sp),
            ExprKind::Name(n) => {
                self.open("name", sp);
                self.s(" ");
                self.s(n);
            }
            ExprKind::Field(x, n) => {
                self.open("field", sp);
                self.s(" ");
                self.expr(x);
                self.s(" ");
                self.s(n);
            }
            ExprKind::TupleField(x, n) => {
                self.open("tfield", sp);
                self.s(" ");
                self.expr(x);
                self.out.push_str(&format!(" {}", n));
            }
            ExprKind::Call(f, args) => {
                self.open("call", sp);
                self.s(" ");
                self.expr(f);
                self.exprs(args);
            }
            ExprKind::Index(x, i) => {
                self.open("index", sp);
                self.s(" ");
                self.expr(x);
                self.s(" ");
                self.expr(i);
            }
            ExprKind::Unary(op, x) => {
                self.open("unary", sp);
                self.s(match op {
                    UnOp::Neg => " neg ",
                    UnOp::Not => " not ",
                    UnOp::Deref => " deref ",
                    UnOp::Addr => " addr ",
                });
                self.expr(x);
            }
            ExprKind::Binary(op, l, r) => {
                self.open("binary", sp);
                self.s(" ");
                self.s(op.text());
                self.s(" ");
                self.expr(l);
                self.s(" ");
                self.expr(r);
            }
            ExprKind::Cast(x, t) => {
                self.open("cast", sp);
                self.s(" ");
                self.expr(x);
                self.s(" ");
                self.ty(t);
            }
            ExprKind::Try(x) => {
                self.open("try", sp);
                self.s(" ");
                self.expr(x);
            }
            ExprKind::Move(x) => {
                self.open("move", sp);
                self.s(" ");
                self.expr(x);
            }
            ExprKind::StructLit(p, fields) => {
                self.open("structlit", sp);
                self.s(" ");
                self.expr(p);
                self.s(" [");
                for (i, (n, v, fsp)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.s(" ");
                    }
                    self.open(n, *fsp);
                    self.s(" ");
                    self.expr(v);
                    self.s(")");
                }
                self.s("]");
            }
            ExprKind::Tuple(xs) => {
                self.open("tuple", sp);
                self.exprs(xs);
            }
            ExprKind::Array(xs) => {
                self.open("array", sp);
                self.exprs(xs);
            }
            ExprKind::ArrayRepeat(x, n) => {
                self.open("repeat", sp);
                self.s(" ");
                self.expr(x);
                self.s(" ");
                self.expr(n);
            }
            ExprKind::Block(b) => {
                self.open("do", sp);
                self.s(" ");
                self.block(b);
            }
            ExprKind::Unsafe(b) => {
                self.open("unsafe", sp);
                self.s(" ");
                self.block(b);
            }
            ExprKind::Comptime(x) => {
                self.open("comptime", sp);
                self.s(" ");
                self.expr(x);
            }
            ExprKind::If(c, then, els) => {
                self.open("if", sp);
                self.s(" ");
                self.expr(c);
                self.s(" ");
                self.block(then);
                self.opt_expr(els.as_deref());
            }
            ExprKind::Match(x, arms) => {
                self.open("match", sp);
                self.s(" ");
                self.expr(x);
                self.s(" [");
                for (i, a) in arms.iter().enumerate() {
                    if i > 0 {
                        self.s(" ");
                    }
                    self.open("arm", a.span);
                    self.s(" ");
                    self.pat(&a.pat);
                    self.opt_expr(a.guard.as_ref());
                    self.s(" ");
                    self.expr(&a.body);
                    self.s(")");
                }
                self.s("]");
            }
            ExprKind::While(c, b) => {
                self.open("while", sp);
                self.s(" ");
                self.expr(c);
                self.s(" ");
                self.block(b);
            }
            ExprKind::Loop(b) => {
                self.open("loop", sp);
                self.s(" ");
                self.block(b);
            }
            ExprKind::For(index, pat, it, b) => {
                self.open("for", sp);
                match index {
                    Some((n, isp)) => {
                        self.s(" ");
                        self.open(n, *isp);
                        self.s(")");
                    }
                    None => self.s(" _"),
                }
                self.s(" ");
                self.pat(pat);
                self.s(" ");
                self.expr(it);
                self.s(" ");
                self.block(b);
            }
            ExprKind::Lambda(params, ret, b) => {
                self.open("lambda", sp);
                self.s(" [");
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        self.s(" ");
                    }
                    self.open(&p.name, p.span);
                    self.opt_ty(&p.ty);
                    self.s(")");
                }
                self.s("]");
                self.opt_ty(ret);
                self.s(" ");
                self.block(b);
            }
            ExprKind::Return(x) => {
                self.open("return", sp);
                self.opt_expr(x.as_deref());
            }
            ExprKind::Break => self.open("break", sp),
            ExprKind::Continue => self.open("continue", sp),
            ExprKind::Range(lo, hi) => {
                self.open("range", sp);
                self.opt_expr(lo.as_deref());
                self.opt_expr(hi.as_deref());
            }
            ExprKind::Type(t) => {
                self.open("type", sp);
                self.s(" ");
                self.ty(t);
            }
        }
        self.s(")");
    }

    fn pat(&mut self, p: &Pat) {
        let sp = p.span;
        match &p.kind {
            PatKind::Wild => self.open("wild", sp),
            PatKind::Name(n, var) => {
                self.open("name", sp);
                self.s(" ");
                self.s(n);
                self.s(if *var { " var" } else { " let" });
            }
            PatKind::Int(v) => {
                self.open("int", sp);
                self.out.push_str(&format!(" {}", v));
            }
            PatKind::Char(c) => {
                self.open("char", sp);
                self.out.push_str(&format!(" {}", c));
            }
            PatKind::Bool(b) => {
                self.open("bool", sp);
                self.s(if *b { " true" } else { " false" });
            }
            PatKind::Str(b) => {
                self.open("str", sp);
                self.bytes(b);
            }
            PatKind::Tuple(ps) => {
                self.open("tuple", sp);
                self.pats(ps);
            }
            PatKind::Variant(path, ps) => {
                self.open("variant", sp);
                self.s(" [");
                self.words(path);
                self.s("]");
                self.pats(ps);
            }
            PatKind::Struct(path, fields, rest) => {
                self.open("struct", sp);
                self.s(" [");
                self.words(path);
                self.s("] [");
                for (i, (n, fp)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.s(" ");
                    }
                    self.s("(");
                    self.s(n);
                    self.s(" ");
                    self.pat(fp);
                    self.s(")");
                }
                self.s(if *rest { "] rest" } else { "] exact" });
            }
            PatKind::Or(ps) => {
                self.open("or", sp);
                self.pats(ps);
            }
            PatKind::Range(lo, hi) => {
                self.open("range", sp);
                self.out.push_str(&format!(" {} {}", lo, hi));
            }
        }
        self.s(")");
    }
}

/// Every module of a loaded program, in the order they were loaded: its
/// name, file and imports, then its tree.
pub fn program(p: &crate::load::Ast) -> String {
    let mut out = format!("(program root {} prelude {})\n", p.root, p.prelude.map(|m| m.to_string()).unwrap_or_else(|| "_".to_string()));
    for (i, m) in p.modules.iter().enumerate() {
        out.push_str(&format!("(file {} {} {} [", i, m.name, m.path.display()));
        for (j, (alias, target, public, span)) in m.imports.iter().enumerate() {
            if j > 0 {
                out.push(' ');
            }
            out.push_str(&format!("(import {} {} {} {}:{})", alias, target, if *public { "pub" } else { "priv" }, span.lo, span.hi));
        }
        out.push_str("])\n");
        out.push_str(&module(&m.ast));
    }
    out
}
