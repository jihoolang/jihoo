// The syntax tree, as the parser builds it. Names are not resolved yet.

use crate::diag::Span;
use crate::lex::Op;

pub struct Module {
    pub file: u32,
    /// `#![freestanding]` and the like.
    pub attrs: Vec<String>,
    pub items: Vec<Item>,
}

#[derive(Clone, Debug)]
pub struct Attr {
    pub name: String,
    pub args: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Item {
    pub span: Span,
    pub public: bool,
    pub attrs: Vec<Attr>,
    pub kind: ItemKind,
}

#[derive(Clone, Debug)]
pub enum ItemKind {
    Import(Import),
    Fn(FnDecl),
    Struct(StructDecl),
    Enum(EnumDecl),
    Impl(ImplDecl),
    Trait(TraitDecl),
    Const(ConstDecl),
    /// `static NAME: T = value`: a global variable, used in `unsafe` code.
    Static(ConstDecl),
    /// `type Name = T`, in an impl (an associated type) or a module (an alias).
    TypeAlias(String, Option<Ty>),
}

#[derive(Clone, Debug)]
pub struct Import {
    pub path: Vec<String>,
    pub alias: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mode {
    /// Borrowed, read only.
    Let,
    Inout,
    Sink,
    Comptime,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RetMode {
    Value,
    /// `-> ref T`: a borrow of part of the first parameter.
    Ref,
    /// `-> inout T`.
    Inout,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FnKind {
    Normal,
    /// `extern fn`: a C function, declared only.
    Extern,
    /// `export fn`: callable from C under its own name.
    Export,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub mode: Mode,
    /// `None` for a bare `self`.
    pub ty: Option<Ty>,
    /// More traits after the first: `comptime T: Ord + Hash`.
    pub bounds: Vec<Ty>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct FnDecl {
    pub name: String,
    pub name_span: Span,
    pub params: Vec<Param>,
    pub ret: Option<Ty>,
    pub ret_mode: RetMode,
    pub body: Option<Block>,
    pub kind: FnKind,
    pub variadic: bool,
    pub is_unsafe: bool,
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: String,
    pub ty: Ty,
    pub public: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct StructDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug)]
pub struct Variant {
    pub name: String,
    pub fields: Vec<Ty>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct EnumDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub variants: Vec<Variant>,
}

#[derive(Clone, Debug)]
pub struct ImplDecl {
    pub params: Vec<Param>,
    pub trait_: Option<Ty>,
    pub self_ty: Ty,
    pub items: Vec<Item>,
}

#[derive(Clone, Debug)]
pub struct TraitDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub supertraits: Vec<Ty>,
    pub items: Vec<Item>,
}

#[derive(Clone, Debug)]
pub struct ConstDecl {
    pub name: String,
    pub ty: Option<Ty>,
    pub value: Expr,
}

#[derive(Clone, Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TyKind {
    /// `a.b.C`, maybe applied: `Vec(i64)`. Arguments are expressions, since
    /// they may be values (`[T; N]`) as well as types.
    Path(Vec<String>, Option<Vec<Expr>>),
    Ptr(Box<Ty>),
    /// `ref T`, `inout T`: borrows, as type arguments of views.
    Ref(Box<Ty>, bool),
    Array(Box<Ty>, Box<Expr>),
    Slice(Box<Ty>),
    Tuple(Vec<Ty>),
    /// `fn(A, inout B) -> R`: a borrowed closure.
    Fn(Vec<(Mode, Ty)>, Option<Box<Ty>>),
    /// `fnptr(A) -> R`.
    FnPtr(Vec<(Mode, Ty)>, Option<Box<Ty>>),
}

#[derive(Clone, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    /// The last expression, if the block ends with one: the block's value.
    pub tail: Option<Box<Expr>>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LetKind {
    Let,
    Var,
    Inout,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    Let { kind: LetKind, pat: Pat, ty: Option<Ty>, value: Expr },
    Assign(Expr, Expr),
    OpAssign(Op, Expr, Expr),
    Expr(Expr),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    Deref,
    /// `&x`: an `inout` argument, or the address of a place.
    Addr,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct LambdaParam {
    pub name: String,
    pub ty: Option<Ty>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Int(u64),
    Float(f64),
    Str(Vec<u8>),
    Char(u8),
    Bool(bool),
    Unit,
    Name(String),
    Field(Box<Expr>, String),
    TupleField(Box<Expr>, u32),
    Call(Box<Expr>, Vec<Expr>),
    Index(Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Binary(Op, Box<Expr>, Box<Expr>),
    Cast(Box<Expr>, Ty),
    Try(Box<Expr>),
    Move(Box<Expr>),
    /// `Path { a: 1, b }`; the path is an expression (`Name`, `m.Name`,
    /// `Pair(i64)`).
    StructLit(Box<Expr>, Vec<(String, Expr, Span)>),
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    ArrayRepeat(Box<Expr>, Box<Expr>),
    Block(Block),
    Unsafe(Block),
    Comptime(Box<Expr>),
    If(Box<Expr>, Block, Option<Box<Expr>>),
    Match(Box<Expr>, Vec<Arm>),
    While(Box<Expr>, Block),
    Loop(Block),
    /// `for i, x in e`: the names, then the iterated expression.
    For(Option<(String, Span)>, Pat, Box<Expr>, Block),
    Lambda(Vec<LambdaParam>, Option<Ty>, Block),
    Return(Option<Box<Expr>>),
    Break,
    Continue,
    /// `a..b`, `a..`, `..b`: in `for` and slices.
    Range(Option<Box<Expr>>, Option<Box<Expr>>),
    /// A type written where an expression was expected (`fn(i64) -> i64`).
    Type(Ty),
}

#[derive(Clone, Debug)]
pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum PatKind {
    Wild,
    /// A name: binds, unless it names a variant without payload. `var x`
    /// makes the binding mutable.
    Name(String, bool),
    Int(i128),
    Char(u8),
    Bool(bool),
    Str(Vec<u8>),
    Tuple(Vec<Pat>),
    /// `Some(x)`, `Shape.Circle(r)`, `opt.None`.
    Variant(Vec<String>, Vec<Pat>),
    Struct(Vec<String>, Vec<(String, Pat)>, bool),
    Or(Vec<Pat>),
    Range(i128, i128),
}
