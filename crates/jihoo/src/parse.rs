// The parser: tokens to a syntax tree. Recursive descent, with precedence
// climbing for binary operators. A statement ends at a newline, `;` or `}`;
// an expression continues onto the next line only after an operator, or
// before a `.`.

use crate::ast::*;
use crate::diag::{Diag, Span};
use crate::lex::{Op, Tok, Token};

const MAX_DEPTH: u32 = 500;

pub struct Parser {
    toks: Vec<Token>,
    i: usize,
    depth: u32,
}

type PResult<T> = Result<T, Diag>;

pub fn parse_module(file: u32, toks: Vec<Token>) -> PResult<Module> {
    let mut p = Parser { toks, i: 0, depth: 0 };
    let mut attrs = Vec::new();
    while p.at(&Tok::HashBang) {
        p.bump();
        p.expect(&Tok::LBracket)?;
        attrs.push(p.ident()?.0);
        p.expect(&Tok::RBracket)?;
    }
    let mut items = Vec::new();
    while !p.at(&Tok::Eof) {
        if p.eat(&Tok::Semi) {
            continue;
        }
        items.push(p.item()?);
    }
    Ok(Module { file, attrs, items })
}

impl Parser {
    fn tok(&self) -> &Tok {
        &self.toks[self.i].tok
    }

    fn peek(&self, n: usize) -> &Tok {
        &self.toks[(self.i + n).min(self.toks.len() - 1)].tok
    }

    fn span(&self) -> Span {
        self.toks[self.i].span
    }

    fn prev_span(&self) -> Span {
        self.toks[self.i.saturating_sub(1)].span
    }

    fn nl(&self) -> bool {
        self.toks[self.i].nl_before
    }

    fn at(&self, t: &Tok) -> bool {
        self.tok() == t
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.i].clone();
        if self.i < self.toks.len() - 1 {
            self.i += 1;
        }
        t
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.at(t) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn err<T>(&self, msg: &str) -> PResult<T> {
        Err(Diag::new(self.span(), msg))
    }

    fn describe(&self) -> String {
        match self.tok() {
            Tok::Ident(s) => format!("`{}`", s),
            Tok::Int(n) => format!("`{}`", n),
            Tok::Float(f) => format!("`{}`", f),
            Tok::Str(_) => "a string".to_string(),
            Tok::Char(_) => "a character".to_string(),
            Tok::Eof => "the end of the file".to_string(),
            t => format!("`{}`", tok_text(t)),
        }
    }

    fn expect(&mut self, t: &Tok) -> PResult<Span> {
        if self.at(t) {
            Ok(self.bump().span)
        } else {
            self.err(&format!("expected `{}`, found {}", tok_text(t), self.describe()))
        }
    }

    fn ident(&mut self) -> PResult<(String, Span)> {
        match self.tok().clone() {
            Tok::Ident(s) => {
                let sp = self.bump().span;
                Ok((s, sp))
            }
            _ => self.err(&format!("expected a name, found {}", self.describe())),
        }
    }

    fn enter(&mut self) -> PResult<()> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return self.err("code is nested too deeply");
        }
        Ok(())
    }

    /// Separators between list elements: a comma, or a newline before the
    /// next element.
    fn sep(&mut self, close: &Tok) -> PResult<bool> {
        if self.eat(&Tok::Comma) || self.eat(&Tok::Semi) {
            return Ok(true);
        }
        if self.at(close) {
            return Ok(false);
        }
        if self.nl() {
            return Ok(true);
        }
        self.err(&format!("expected `,` or `{}`, found {}", tok_text(close), self.describe()))
    }

    // ---- items ----

    fn attrs(&mut self) -> PResult<Vec<Attr>> {
        let mut out = Vec::new();
        while self.at(&Tok::Hash) {
            let start = self.bump().span;
            self.expect(&Tok::LBracket)?;
            let (name, _) = self.ident()?;
            let mut args = Vec::new();
            if self.eat(&Tok::LParen) {
                while !self.at(&Tok::RParen) {
                    args.push(self.ident()?.0);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(&Tok::RParen)?;
            }
            let end = self.expect(&Tok::RBracket)?;
            out.push(Attr { name, args, span: start.to(end) });
        }
        Ok(out)
    }

    fn item(&mut self) -> PResult<Item> {
        let attrs = self.attrs()?;
        let start = self.span();
        let public = self.eat(&Tok::Pub);
        let kind = match self.tok() {
            Tok::Import => {
                self.bump();
                let mut path = vec![self.ident()?.0];
                while self.eat(&Tok::Dot) {
                    path.push(self.ident()?.0);
                }
                let alias = if self.eat(&Tok::As) { Some(self.ident()?.0) } else { None };
                ItemKind::Import(Import { path, alias })
            }
            Tok::Fn | Tok::Extern | Tok::Export | Tok::Unsafe => ItemKind::Fn(self.fn_decl()?),
            Tok::Struct => {
                self.bump();
                let (name, _) = self.ident()?;
                let params = self.generic_params()?;
                self.expect(&Tok::LBrace)?;
                let mut fields = Vec::new();
                while !self.at(&Tok::RBrace) {
                    let fs = self.span();
                    let public = self.eat(&Tok::Pub);
                    let (fname, _) = self.ident()?;
                    self.expect(&Tok::Colon)?;
                    let ty = self.ty()?;
                    fields.push(Field { name: fname, ty, public, span: fs.to(self.prev_span()) });
                    if !self.sep(&Tok::RBrace)? {
                        break;
                    }
                }
                self.expect(&Tok::RBrace)?;
                ItemKind::Struct(StructDecl { name, params, fields })
            }
            Tok::Enum => {
                self.bump();
                let (name, _) = self.ident()?;
                let params = self.generic_params()?;
                self.expect(&Tok::LBrace)?;
                let mut variants = Vec::new();
                while !self.at(&Tok::RBrace) {
                    let (vname, vs) = self.ident()?;
                    let mut fields = Vec::new();
                    if self.eat(&Tok::LParen) {
                        while !self.at(&Tok::RParen) {
                            fields.push(self.ty()?);
                            if !self.eat(&Tok::Comma) {
                                break;
                            }
                        }
                        self.expect(&Tok::RParen)?;
                    }
                    variants.push(Variant { name: vname, fields, span: vs.to(self.prev_span()) });
                    if !self.sep(&Tok::RBrace)? {
                        break;
                    }
                }
                self.expect(&Tok::RBrace)?;
                ItemKind::Enum(EnumDecl { name, params, variants })
            }
            Tok::Impl => {
                self.bump();
                let params = if self.at(&Tok::LParen) { self.param_list()?.0 } else { Vec::new() };
                let first = self.ty()?;
                let (trait_, self_ty) = if self.at(&Tok::For) {
                    self.bump();
                    (Some(first), self.ty()?)
                } else {
                    (None, first)
                };
                let items = self.item_block()?;
                ItemKind::Impl(ImplDecl { params, trait_, self_ty, items })
            }
            Tok::Trait => {
                self.bump();
                let (name, _) = self.ident()?;
                let params = self.generic_params()?;
                let mut supertraits = Vec::new();
                if self.eat(&Tok::Colon) {
                    supertraits.push(self.ty()?);
                    while self.eat(&Tok::Plus) {
                        supertraits.push(self.ty()?);
                    }
                }
                let items = self.item_block()?;
                ItemKind::Trait(TraitDecl { name, params, supertraits, items })
            }
            Tok::Const | Tok::Static => {
                let is_static = self.bump().tok == Tok::Static;
                let (name, _) = self.ident()?;
                let ty = if self.eat(&Tok::Colon) { Some(self.ty()?) } else { None };
                self.expect(&Tok::Assign)?;
                let value = self.expr()?;
                if is_static {
                    ItemKind::Static(ConstDecl { name, ty, value })
                } else {
                    ItemKind::Const(ConstDecl { name, ty, value })
                }
            }
            Tok::Type => {
                self.bump();
                let (name, _) = self.ident()?;
                let ty = if self.eat(&Tok::Assign) { Some(self.ty()?) } else { None };
                ItemKind::TypeAlias(name, ty)
            }
            _ => return self.err(&format!("expected an item (`fn`, `struct`, `enum`, `impl`, ...), found {}", self.describe())),
        };
        Ok(Item { span: start.to(self.prev_span()), public, attrs, kind })
    }

    fn item_block(&mut self) -> PResult<Vec<Item>> {
        self.expect(&Tok::LBrace)?;
        let mut items = Vec::new();
        while !self.at(&Tok::RBrace) {
            if self.eat(&Tok::Semi) {
                continue;
            }
            items.push(self.item()?);
        }
        self.expect(&Tok::RBrace)?;
        Ok(items)
    }

    fn generic_params(&mut self) -> PResult<Vec<Param>> {
        if !self.at(&Tok::LParen) {
            return Ok(Vec::new());
        }
        let (mut ps, _) = self.param_list()?;
        for p in &mut ps {
            p.mode = Mode::Comptime;
        }
        Ok(ps)
    }

    fn fn_decl(&mut self) -> PResult<FnDecl> {
        let mut kind = FnKind::Normal;
        let is_unsafe = self.eat(&Tok::Unsafe);
        if self.eat(&Tok::Extern) {
            kind = FnKind::Extern;
        } else if self.eat(&Tok::Export) {
            kind = FnKind::Export;
        }
        self.expect(&Tok::Fn)?;
        let (name, name_span) = self.ident()?;
        let (params, variadic) = self.param_list()?;
        let mut ret = None;
        let mut ret_mode = RetMode::Value;
        if self.eat(&Tok::Arrow) {
            if self.eat(&Tok::Ref) {
                ret_mode = RetMode::Ref;
            } else if self.eat(&Tok::Inout) {
                ret_mode = RetMode::Inout;
            }
            ret = Some(self.ty()?);
        }
        let body = if self.at(&Tok::LBrace) { Some(self.block()?) } else { None };
        if variadic && kind != FnKind::Extern {
            return Err(Diag::new(name_span, "only extern functions can have `...` parameters"));
        }
        if kind == FnKind::Extern && body.is_some() {
            return Err(Diag::new(name_span, "an extern function cannot have a body; use `export fn` to define a C function"));
        }
        Ok(FnDecl { name, name_span, params, ret, ret_mode, body, kind, variadic, is_unsafe })
    }

    fn param_list(&mut self) -> PResult<(Vec<Param>, bool)> {
        self.expect(&Tok::LParen)?;
        let mut params = Vec::new();
        let mut variadic = false;
        while !self.at(&Tok::RParen) {
            if self.eat(&Tok::Ellipsis) {
                variadic = true;
                break;
            }
            let start = self.span();
            let mode = match self.tok() {
                Tok::Inout => {
                    self.bump();
                    Mode::Inout
                }
                Tok::Sink => {
                    self.bump();
                    Mode::Sink
                }
                Tok::Comptime => {
                    self.bump();
                    Mode::Comptime
                }
                _ => Mode::Let,
            };
            let (name, _) = self.ident()?;
            let mut ty = None;
            let mut bounds = Vec::new();
            if self.eat(&Tok::Colon) {
                ty = Some(self.ty()?);
                while self.eat(&Tok::Plus) {
                    bounds.push(self.ty()?);
                }
            } else if name != "self" {
                return self.err("expected `:` and the parameter's type");
            }
            params.push(Param { name, mode, ty, bounds, span: start.to(self.prev_span()) });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RParen)?;
        Ok((params, variadic))
    }

    // ---- types ----

    pub fn ty(&mut self) -> PResult<Ty> {
        self.enter()?;
        let start = self.span();
        let kind = match self.tok().clone() {
            Tok::Star => {
                self.bump();
                TyKind::Ptr(Box::new(self.ty()?))
            }
            Tok::LBracket => {
                self.bump();
                let elem = self.ty()?;
                if self.eat(&Tok::Semi) {
                    let n = self.expr()?;
                    self.expect(&Tok::RBracket)?;
                    TyKind::Array(Box::new(elem), Box::new(n))
                } else {
                    self.expect(&Tok::RBracket)?;
                    TyKind::Slice(Box::new(elem))
                }
            }
            Tok::LParen => {
                self.bump();
                let mut tys = Vec::new();
                while !self.at(&Tok::RParen) {
                    tys.push(self.ty()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(&Tok::RParen)?;
                if tys.len() == 1 {
                    self.depth -= 1;
                    return Ok(tys.pop().unwrap());
                }
                TyKind::Tuple(tys)
            }
            Tok::Fn => {
                self.bump();
                let (ps, r) = self.fn_ty_rest()?;
                TyKind::Fn(ps, r)
            }
            Tok::Type => {
                self.bump();
                TyKind::Path(vec!["type".to_string()], None)
            }
            Tok::Ref | Tok::Inout => {
                let m = self.bump().tok == Tok::Inout;
                TyKind::Ref(Box::new(self.ty()?), m)
            }
            Tok::Ident(s) if s == "fnptr" && self.peek(1) == &Tok::LParen => {
                self.bump();
                let (ps, r) = self.fn_ty_rest()?;
                TyKind::FnPtr(ps, r)
            }
            Tok::Ident(_) => {
                let mut path = vec![self.ident()?.0];
                while self.at(&Tok::Dot) && matches!(self.peek(1), Tok::Ident(_)) {
                    self.bump();
                    path.push(self.ident()?.0);
                }
                let args = if self.at(&Tok::LParen) && !self.nl() { Some(self.call_args()?) } else { None };
                TyKind::Path(path, args)
            }
            _ => return self.err(&format!("expected a type, found {}", self.describe())),
        };
        self.depth -= 1;
        Ok(Ty { kind, span: start.to(self.prev_span()) })
    }

    fn param_mode(&mut self) -> Mode {
        if self.eat(&Tok::Inout) {
            Mode::Inout
        } else if self.eat(&Tok::Sink) {
            Mode::Sink
        } else {
            Mode::Let
        }
    }

    fn fn_ty_rest(&mut self) -> PResult<(Vec<(Mode, Ty)>, Option<Box<Ty>>)> {
        self.expect(&Tok::LParen)?;
        let mut ps = Vec::new();
        while !self.at(&Tok::RParen) {
            let m = self.param_mode();
            ps.push((m, self.ty()?));
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RParen)?;
        let r = if self.at(&Tok::Arrow) && !self.nl() {
            self.bump();
            Some(Box::new(self.ty()?))
        } else {
            None
        };
        Ok((ps, r))
    }

    // ---- statements ----

    pub fn block(&mut self) -> PResult<Block> {
        self.enter()?;
        let start = self.expect(&Tok::LBrace)?;
        let mut stmts = Vec::new();
        let mut tail = None;
        loop {
            while self.eat(&Tok::Semi) {}
            if self.at(&Tok::RBrace) {
                break;
            }
            let s = self.stmt()?;
            let ended_semi = self.at(&Tok::Semi);
            if !self.at(&Tok::RBrace) && !self.at(&Tok::Semi) && !self.nl() {
                return self.err(&format!("expected the end of the statement, found {}", self.describe()));
            }
            if self.at(&Tok::RBrace) && !ended_semi {
                if let StmtKind::Expr(e) = s.kind {
                    tail = Some(Box::new(e));
                    break;
                }
            }
            stmts.push(s);
        }
        let end = self.expect(&Tok::RBrace)?;
        self.depth -= 1;
        Ok(Block { stmts, tail, span: start.to(end) })
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let start = self.span();
        let kind = match self.tok() {
            Tok::Let | Tok::Var | Tok::Inout => {
                let kind = match self.bump().tok {
                    Tok::Let => LetKind::Let,
                    Tok::Var => LetKind::Var,
                    _ => LetKind::Inout,
                };
                let pat = self.pattern()?;
                let ty = if self.eat(&Tok::Colon) { Some(self.ty()?) } else { None };
                self.expect(&Tok::Assign)?;
                let value = self.expr()?;
                StmtKind::Let { kind, pat, ty, value }
            }
            _ => {
                let e = self.expr()?;
                match self.tok().clone() {
                    Tok::Assign if !self.nl() => {
                        self.bump();
                        let v = self.expr()?;
                        StmtKind::Assign(e, v)
                    }
                    Tok::OpAssign(op) if !self.nl() => {
                        self.bump();
                        let v = self.expr()?;
                        StmtKind::OpAssign(op, e, v)
                    }
                    _ => StmtKind::Expr(e),
                }
            }
        };
        Ok(Stmt { kind, span: start.to(self.prev_span()) })
    }

    // ---- expressions ----

    pub fn expr(&mut self) -> PResult<Expr> {
        self.expr_bp(0, false)
    }

    /// An expression where a struct literal cannot start (`if x {`).
    fn expr_ns(&mut self) -> PResult<Expr> {
        self.expr_bp(0, true)
    }

    fn binop(&self) -> Option<(Op, u8)> {
        if self.nl() {
            return None;
        }
        Some(match self.tok() {
            Tok::OrOr => (Op::LogOr, 1),
            Tok::AndAnd => (Op::LogAnd, 2),
            Tok::EqEq => (Op::Eq, 3),
            Tok::NotEq => (Op::Ne, 3),
            Tok::Lt => (Op::Lt, 3),
            Tok::Le => (Op::Le, 3),
            Tok::Gt => (Op::Gt, 3),
            Tok::Ge => (Op::Ge, 3),
            Tok::Pipe => (Op::Or, 4),
            Tok::Caret => (Op::Xor, 5),
            Tok::Amp => (Op::And, 6),
            Tok::Shl => (Op::Shl, 7),
            Tok::Shr => (Op::Shr, 7),
            Tok::Plus => (Op::Add, 8),
            Tok::Minus => (Op::Sub, 8),
            Tok::PlusWrap => (Op::AddWrap, 8),
            Tok::MinusWrap => (Op::SubWrap, 8),
            Tok::Star => (Op::Mul, 9),
            Tok::Slash => (Op::Div, 9),
            Tok::Percent => (Op::Rem, 9),
            Tok::StarWrap => (Op::MulWrap, 9),
            _ => return None,
        })
    }

    fn expr_bp(&mut self, min: u8, ns: bool) -> PResult<Expr> {
        self.enter()?;
        let start = self.span();
        if self.at(&Tok::DotDot) {
            self.bump();
            let hi = if self.range_end() { None } else { Some(Box::new(self.expr_bp(1, ns)?)) };
            self.depth -= 1;
            return Ok(Expr { kind: ExprKind::Range(None, hi), span: start.to(self.prev_span()) });
        }
        let mut lhs = self.unary(ns)?;
        loop {
            if self.at(&Tok::As) && !self.nl() {
                self.bump();
                let t = self.ty()?;
                lhs = Expr { span: lhs.span.to(t.span), kind: ExprKind::Cast(Box::new(lhs), t) };
                continue;
            }
            if min == 0 && self.at(&Tok::DotDot) && !self.nl() {
                self.bump();
                let hi = if self.range_end() { None } else { Some(Box::new(self.expr_bp(1, ns)?)) };
                lhs = Expr { span: start.to(self.prev_span()), kind: ExprKind::Range(Some(Box::new(lhs)), hi) };
                break;
            }
            let Some((op, prec)) = self.binop() else { break };
            if prec <= min {
                break;
            }
            let opspan = self.bump().span;
            let rhs = self.expr_bp(prec, ns)?;
            if op.is_compare() {
                if let Some((op2, p2)) = self.binop() {
                    if p2 == prec && op2.is_compare() {
                        return Err(Diag::new(self.span(), "comparisons do not chain; use `&&`"));
                    }
                }
            }
            let _ = opspan;
            lhs = Expr { span: lhs.span.to(rhs.span), kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)) };
        }
        self.depth -= 1;
        Ok(lhs)
    }

    fn range_end(&self) -> bool {
        matches!(self.tok(), Tok::RBracket | Tok::RParen | Tok::LBrace | Tok::Comma) || self.nl()
    }

    fn unary(&mut self, ns: bool) -> PResult<Expr> {
        let start = self.span();
        let op = match self.tok() {
            Tok::Minus => Some(UnOp::Neg),
            Tok::Bang => Some(UnOp::Not),
            Tok::Star => Some(UnOp::Deref),
            Tok::Amp => Some(UnOp::Addr),
            _ => None,
        };
        if let Some(op) = op {
            self.bump();
            self.enter()?;
            let e = self.unary(ns)?;
            self.depth -= 1;
            return Ok(Expr { span: start.to(e.span), kind: ExprKind::Unary(op, Box::new(e)) });
        }
        if self.eat(&Tok::Move) {
            let e = self.unary(ns)?;
            return Ok(Expr { span: start.to(e.span), kind: ExprKind::Move(Box::new(e)) });
        }
        let e = self.primary(ns)?;
        self.postfix(e, ns)
    }

    fn call_args(&mut self) -> PResult<Vec<Expr>> {
        self.expect(&Tok::LParen)?;
        let mut args = Vec::new();
        while !self.at(&Tok::RParen) {
            args.push(self.expr()?);
            if !self.sep(&Tok::RParen)? {
                break;
            }
        }
        self.expect(&Tok::RParen)?;
        Ok(args)
    }

    fn postfix(&mut self, mut e: Expr, ns: bool) -> PResult<Expr> {
        loop {
            match self.tok() {
                Tok::LParen if !self.nl() => {
                    let args = self.call_args()?;
                    e = Expr { span: e.span.to(self.prev_span()), kind: ExprKind::Call(Box::new(e), args) };
                }
                Tok::LBracket if !self.nl() => {
                    self.bump();
                    let idx = self.expr()?;
                    self.expect(&Tok::RBracket)?;
                    e = Expr { span: e.span.to(self.prev_span()), kind: ExprKind::Index(Box::new(e), Box::new(idx)) };
                }
                Tok::Dot => {
                    self.bump();
                    match self.tok().clone() {
                        Tok::Int(n) => {
                            self.bump();
                            e = Expr { span: e.span.to(self.prev_span()), kind: ExprKind::TupleField(Box::new(e), n as u32) };
                        }
                        _ => {
                            let (name, _) = self.ident()?;
                            e = Expr { span: e.span.to(self.prev_span()), kind: ExprKind::Field(Box::new(e), name) };
                        }
                    }
                }
                Tok::Question if !self.nl() => {
                    self.bump();
                    e = Expr { span: e.span.to(self.prev_span()), kind: ExprKind::Try(Box::new(e)) };
                }
                Tok::LBrace if !ns && !self.nl() && is_path_expr(&e) && self.struct_lit_ahead() => {
                    e = self.struct_lit(e)?;
                }
                _ => return Ok(e),
            }
        }
    }

    /// After `Name {`: a struct literal starts with `}` or `name:` or `name,`.
    fn struct_lit_ahead(&self) -> bool {
        matches!((self.peek(1), self.peek(2)), (Tok::RBrace, _) | (Tok::Ident(_), Tok::Colon | Tok::Comma | Tok::RBrace))
    }

    fn struct_lit(&mut self, path: Expr) -> PResult<Expr> {
        self.expect(&Tok::LBrace)?;
        let mut fields = Vec::new();
        while !self.at(&Tok::RBrace) {
            let (name, sp) = self.ident()?;
            let value = if self.eat(&Tok::Colon) { self.expr()? } else { Expr { kind: ExprKind::Name(name.clone()), span: sp } };
            fields.push((name, value, sp));
            if !self.sep(&Tok::RBrace)? {
                break;
            }
        }
        let end = self.expect(&Tok::RBrace)?;
        Ok(Expr { span: path.span.to(end), kind: ExprKind::StructLit(Box::new(path), fields) })
    }

    fn primary(&mut self, ns: bool) -> PResult<Expr> {
        let start = self.span();
        let t = self.tok().clone();
        let kind = match t {
            Tok::Int(n) => {
                self.bump();
                ExprKind::Int(n)
            }
            Tok::Float(f) => {
                self.bump();
                ExprKind::Float(f)
            }
            Tok::Str(s) => {
                self.bump();
                ExprKind::Str(s)
            }
            Tok::Char(c) => {
                self.bump();
                ExprKind::Char(c)
            }
            Tok::True => {
                self.bump();
                ExprKind::Bool(true)
            }
            Tok::False => {
                self.bump();
                ExprKind::Bool(false)
            }
            Tok::Ident(s) => {
                if s == "fnptr" && self.peek(1) == &Tok::LParen {
                    let ty = self.ty()?;
                    ExprKind::Type(ty)
                } else {
                    self.bump();
                    ExprKind::Name(s)
                }
            }
            Tok::Type => {
                self.bump();
                ExprKind::Name("type".to_string())
            }
            Tok::Ref | Tok::Inout => {
                let ty = self.ty()?;
                ExprKind::Type(ty)
            }
            Tok::LParen => {
                self.bump();
                if self.eat(&Tok::RParen) {
                    ExprKind::Unit
                } else {
                    let first = self.expr()?;
                    if self.eat(&Tok::RParen) {
                        return Ok(Expr { kind: first.kind, span: start.to(self.prev_span()) });
                    }
                    let mut items = vec![first];
                    while self.eat(&Tok::Comma) {
                        if self.at(&Tok::RParen) {
                            break;
                        }
                        items.push(self.expr()?);
                    }
                    self.expect(&Tok::RParen)?;
                    ExprKind::Tuple(items)
                }
            }
            Tok::LBracket => {
                self.bump();
                if self.eat(&Tok::RBracket) {
                    ExprKind::Array(Vec::new())
                } else {
                    let first = self.expr()?;
                    if self.eat(&Tok::Semi) {
                        let n = self.expr()?;
                        self.expect(&Tok::RBracket)?;
                        ExprKind::ArrayRepeat(Box::new(first), Box::new(n))
                    } else {
                        let mut items = vec![first];
                        while self.sep(&Tok::RBracket)? {
                            if self.at(&Tok::RBracket) {
                                break;
                            }
                            items.push(self.expr()?);
                        }
                        self.expect(&Tok::RBracket)?;
                        ExprKind::Array(items)
                    }
                }
            }
            Tok::LBrace => ExprKind::Block(self.block()?),
            Tok::Unsafe => {
                self.bump();
                ExprKind::Unsafe(self.block()?)
            }
            Tok::Comptime => {
                self.bump();
                let e = self.unary(ns)?;
                ExprKind::Comptime(Box::new(e))
            }
            Tok::If => return self.if_expr(),
            Tok::Match => {
                self.bump();
                let scrut = self.expr_ns()?;
                self.expect(&Tok::LBrace)?;
                let mut arms = Vec::new();
                while !self.at(&Tok::RBrace) {
                    let astart = self.span();
                    let pat = self.pattern()?;
                    let guard = if self.eat(&Tok::If) { Some(self.expr()?) } else { None };
                    self.expect(&Tok::FatArrow)?;
                    let body = self.arm_body()?;
                    arms.push(Arm { pat, guard, body, span: astart.to(self.prev_span()) });
                    if !self.sep(&Tok::RBrace)? {
                        break;
                    }
                }
                self.expect(&Tok::RBrace)?;
                ExprKind::Match(Box::new(scrut), arms)
            }
            Tok::While => {
                self.bump();
                let c = self.expr_ns()?;
                let b = self.block()?;
                ExprKind::While(Box::new(c), b)
            }
            Tok::Loop => {
                self.bump();
                ExprKind::Loop(self.block()?)
            }
            Tok::For => {
                self.bump();
                let first = self.pattern()?;
                let (index, pat) = if self.eat(&Tok::Comma) {
                    let PatKind::Name(n, false) = &first.kind else {
                        return Err(Diag::new(first.span, "the index of a `for` loop is a name"));
                    };
                    (Some((n.clone(), first.span)), self.pattern()?)
                } else {
                    (None, first)
                };
                self.expect(&Tok::In)?;
                let it = self.expr_ns()?;
                let b = self.block()?;
                ExprKind::For(index, pat, Box::new(it), b)
            }
            Tok::Fn => return self.lambda_or_type(),
            Tok::Return => {
                self.bump();
                let v = if self.at(&Tok::RBrace) || self.nl() || self.at(&Tok::Semi) || self.at(&Tok::Comma) {
                    None
                } else {
                    Some(Box::new(self.expr()?))
                };
                ExprKind::Return(v)
            }
            Tok::Break => {
                self.bump();
                ExprKind::Break
            }
            Tok::Continue => {
                self.bump();
                ExprKind::Continue
            }
            _ => return self.err(&format!("expected an expression, found {}", self.describe())),
        };
        Ok(Expr { kind, span: start.to(self.prev_span()) })
    }

    /// An arm's body: an expression, or a statement (`x => n += 1`).
    fn arm_body(&mut self) -> PResult<Expr> {
        let s = self.stmt()?;
        match s.kind {
            StmtKind::Expr(e) => Ok(e),
            _ => {
                let span = s.span;
                Ok(Expr { kind: ExprKind::Block(Block { stmts: vec![s], tail: None, span }), span })
            }
        }
    }

    fn if_expr(&mut self) -> PResult<Expr> {
        let start = self.expect(&Tok::If)?;
        let c = self.expr_ns()?;
        let then = self.block()?;
        let els = if self.at(&Tok::Else) {
            self.bump();
            if self.at(&Tok::If) {
                Some(Box::new(self.if_expr()?))
            } else {
                let b = self.block()?;
                Some(Box::new(Expr { span: b.span, kind: ExprKind::Block(b) }))
            }
        } else {
            None
        };
        Ok(Expr { kind: ExprKind::If(Box::new(c), then, els), span: start.to(self.prev_span()) })
    }

    /// `fn(x, y: i64) -> T { ... }` is a closure; `fn(i64) -> T` is a type.
    fn lambda_or_type(&mut self) -> PResult<Expr> {
        let start = self.expect(&Tok::Fn)?;
        self.expect(&Tok::LParen)?;
        enum Entry {
            Named(LambdaParam),
            Ty(Mode, Ty),
        }
        let mut entries = Vec::new();
        while !self.at(&Tok::RParen) {
            if let (Tok::Ident(n), Tok::Colon) = (self.tok().clone(), self.peek(1).clone()) {
                let sp = self.bump().span;
                self.bump();
                let ty = self.ty()?;
                entries.push(Entry::Named(LambdaParam { name: n, ty: Some(ty), span: sp }));
            } else {
                let m = self.param_mode();
                entries.push(Entry::Ty(m, self.ty()?));
            }
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RParen)?;
        let ret = if self.at(&Tok::Arrow) && !self.nl() {
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
        if self.at(&Tok::LBrace) {
            let mut params = Vec::new();
            for e in entries {
                match e {
                    Entry::Named(p) => params.push(p),
                    Entry::Ty(Mode::Let, Ty { kind: TyKind::Path(p, None), span }) if p.len() == 1 => {
                        params.push(LambdaParam { name: p[0].clone(), ty: None, span })
                    }
                    Entry::Ty(_, t) => return Err(Diag::new(t.span, "expected a parameter name")),
                }
            }
            let body = self.block()?;
            return Ok(Expr { kind: ExprKind::Lambda(params, ret, body), span: start.to(self.prev_span()) });
        }
        let mut tys = Vec::new();
        for e in entries {
            match e {
                Entry::Ty(m, t) => tys.push((m, t)),
                Entry::Named(p) => return Err(Diag::new(p.span, "a function type lists types, not names")),
            }
        }
        let span = start.to(self.prev_span());
        Ok(Expr { kind: ExprKind::Type(Ty { kind: TyKind::Fn(tys, ret.map(Box::new)), span }), span })
    }

    // ---- patterns ----

    pub fn pattern(&mut self) -> PResult<Pat> {
        self.enter()?;
        let start = self.span();
        let first = self.single_pattern()?;
        if !self.at(&Tok::Pipe) {
            self.depth -= 1;
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(&Tok::Pipe) {
            alts.push(self.single_pattern()?);
        }
        self.depth -= 1;
        Ok(Pat { kind: PatKind::Or(alts), span: start.to(self.prev_span()) })
    }

    fn pat_int(&mut self) -> PResult<Option<i128>> {
        let neg = self.at(&Tok::Minus);
        let save = self.i;
        if neg {
            self.bump();
        }
        let v = match self.tok() {
            Tok::Int(n) => *n as i128,
            Tok::Char(c) => *c as i128,
            _ => {
                self.i = save;
                return Ok(None);
            }
        };
        self.bump();
        Ok(Some(if neg { -v } else { v }))
    }

    fn single_pattern(&mut self) -> PResult<Pat> {
        let start = self.span();
        let is_char = matches!(self.tok(), Tok::Char(_));
        if let Some(v) = self.pat_int()? {
            if self.at(&Tok::DotDot) {
                self.bump();
                self.eat(&Tok::Assign);
                let Some(hi) = self.pat_int()? else { return self.err("expected the end of the range") };
                return Ok(Pat { kind: PatKind::Range(v, hi), span: start.to(self.prev_span()) });
            }
            let kind = if is_char { PatKind::Char(v as u8) } else { PatKind::Int(v) };
            return Ok(Pat { kind, span: start.to(self.prev_span()) });
        }
        let kind = match self.tok().clone() {
            Tok::True => {
                self.bump();
                PatKind::Bool(true)
            }
            Tok::False => {
                self.bump();
                PatKind::Bool(false)
            }
            Tok::Str(s) => {
                self.bump();
                PatKind::Str(s)
            }
            Tok::Var => {
                self.bump();
                let (n, _) = self.ident()?;
                PatKind::Name(n, true)
            }
            Tok::LParen => {
                self.bump();
                let mut ps = Vec::new();
                while !self.at(&Tok::RParen) {
                    ps.push(self.pattern()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(&Tok::RParen)?;
                if ps.len() == 1 {
                    return Ok(ps.pop().unwrap());
                }
                PatKind::Tuple(ps)
            }
            Tok::Ident(n) if n == "_" => {
                self.bump();
                PatKind::Wild
            }
            Tok::Ident(_) => {
                let mut path = vec![self.ident()?.0];
                while self.at(&Tok::Dot) {
                    self.bump();
                    path.push(self.ident()?.0);
                }
                if self.at(&Tok::LParen) {
                    self.bump();
                    let mut ps = Vec::new();
                    while !self.at(&Tok::RParen) {
                        ps.push(self.pattern()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(&Tok::RParen)?;
                    PatKind::Variant(path, ps)
                } else if self.at(&Tok::LBrace) {
                    self.bump();
                    let mut fields = Vec::new();
                    let mut rest = false;
                    while !self.at(&Tok::RBrace) {
                        if self.eat(&Tok::DotDot) {
                            rest = true;
                            break;
                        }
                        let (f, sp) = self.ident()?;
                        let p = if self.eat(&Tok::Colon) { self.pattern()? } else { Pat { kind: PatKind::Name(f.clone(), false), span: sp } };
                        fields.push((f, p));
                        if !self.sep(&Tok::RBrace)? {
                            break;
                        }
                    }
                    self.expect(&Tok::RBrace)?;
                    PatKind::Struct(path, fields, rest)
                } else if path.len() == 1 {
                    PatKind::Name(path.pop().unwrap(), false)
                } else {
                    PatKind::Variant(path, Vec::new())
                }
            }
            _ => return self.err(&format!("expected a pattern, found {}", self.describe())),
        };
        Ok(Pat { kind, span: start.to(self.prev_span()) })
    }
}

fn is_path_expr(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Name(_) => true,
        ExprKind::Field(b, _) => is_path_expr(b),
        ExprKind::Call(b, _) => is_path_expr(b),
        _ => false,
    }
}

pub fn tok_text(t: &Tok) -> String {
    match t {
        Tok::Ident(s) => s.clone(),
        Tok::Int(n) => n.to_string(),
        Tok::Float(f) => f.to_string(),
        Tok::Str(_) => "string".into(),
        Tok::Char(_) => "character".into(),
        Tok::OpAssign(op) => format!("{}=", op.text()),
        t => match t {
            Tok::Fn => "fn",
            Tok::Let => "let",
            Tok::Var => "var",
            Tok::Return => "return",
            Tok::If => "if",
            Tok::Else => "else",
            Tok::While => "while",
            Tok::Loop => "loop",
            Tok::For => "for",
            Tok::In => "in",
            Tok::Break => "break",
            Tok::Continue => "continue",
            Tok::True => "true",
            Tok::False => "false",
            Tok::Struct => "struct",
            Tok::Enum => "enum",
            Tok::Match => "match",
            Tok::Impl => "impl",
            Tok::Trait => "trait",
            Tok::Pub => "pub",
            Tok::Import => "import",
            Tok::As => "as",
            Tok::Const => "const",
            Tok::Comptime => "comptime",
            Tok::Extern => "extern",
            Tok::Export => "export",
            Tok::Unsafe => "unsafe",
            Tok::Sink => "sink",
            Tok::Inout => "inout",
            Tok::Ref => "ref",
            Tok::Move => "move",
            Tok::Type => "type",
            Tok::Static => "static",
            Tok::LParen => "(",
            Tok::RParen => ")",
            Tok::LBrace => "{",
            Tok::RBrace => "}",
            Tok::LBracket => "[",
            Tok::RBracket => "]",
            Tok::Dot => ".",
            Tok::DotDot => "..",
            Tok::Ellipsis => "...",
            Tok::Comma => ",",
            Tok::Colon => ":",
            Tok::Semi => ";",
            Tok::Arrow => "->",
            Tok::FatArrow => "=>",
            Tok::Question => "?",
            Tok::Hash => "#",
            Tok::HashBang => "#!",
            Tok::Assign => "=",
            Tok::EqEq => "==",
            Tok::NotEq => "!=",
            Tok::Lt => "<",
            Tok::Le => "<=",
            Tok::Gt => ">",
            Tok::Ge => ">=",
            Tok::Plus => "+",
            Tok::Minus => "-",
            Tok::Star => "*",
            Tok::Slash => "/",
            Tok::Percent => "%",
            Tok::PlusWrap => "+%",
            Tok::MinusWrap => "-%",
            Tok::StarWrap => "*%",
            Tok::Amp => "&",
            Tok::Pipe => "|",
            Tok::Caret => "^",
            Tok::Shl => "<<",
            Tok::Shr => ">>",
            Tok::Bang => "!",
            Tok::AndAnd => "&&",
            Tok::OrOr => "||",
            Tok::Eof => "end of file",
            _ => "?",
        }
        .to_string(),
    }
}
