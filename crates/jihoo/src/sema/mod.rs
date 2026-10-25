// Sema: names, types, generic instances, and lowering to MIR, in one pass
// over each function instance. Generic code is checked per instance, as in
// Zig: an instance is a declaration and its compile-time arguments.

mod body;
mod builtins;
mod consts;
mod pat;

use crate::ast::{self, Mode, RetMode};
use crate::diag::{Diag, Span};
use crate::load::Ast;
use crate::mir::{self, FnId, Linkage, ParamPass};
use crate::types::{self, AdtBody, FieldDef, Sig, TyId, TyKind, Types, VariantDef};
use std::collections::{HashMap, VecDeque};

pub type R<T> = Result<T, Diag>;

/// A compile-time value: a generic argument or a constant.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CVal {
    Type(TyId),
    Int(i128),
    Bool(bool),
    /// A closure passed to a `comptime` parameter: its lifted function and
    /// its environment's type.
    Lambda(FnId, TyId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sym {
    Fn(u32),
    Adt(u32),
    Trait(u32),
    Const(u32),
    Module(u32),
    Alias(u32),
    Static(u32),
}

pub struct ModScope {
    pub names: HashMap<String, (Sym, bool)>,
    /// Modules whose public names this one sees too (the prelude's).
    pub globs: Vec<u32>,
}

#[derive(Clone, Copy)]
pub enum AdtKind<'a> {
    Struct(&'a ast::StructDecl),
    Enum(&'a ast::EnumDecl),
}

pub struct AdtDecl<'a> {
    pub module: u32,
    pub name: String,
    pub kind: AdtKind<'a>,
    pub span: Span,
    pub derives: Vec<String>,
    pub impls: Vec<u32>,
    /// `#[view]`: holds borrows through raw pointers.
    pub is_view: bool,
}

impl AdtDecl<'_> {
    pub fn params(&self) -> &[ast::Param] {
        match self.kind {
            AdtKind::Struct(s) => &s.params,
            AdtKind::Enum(e) => &e.params,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Owner {
    Free,
    Impl(u32),
    Trait(u32),
}

pub struct FnDeclInfo<'a> {
    pub module: u32,
    pub decl: &'a ast::FnDecl,
    pub span: Span,
    pub public: bool,
    pub owner: Owner,
}

pub struct ImplInfo<'a> {
    pub module: u32,
    pub decl: &'a ast::ImplDecl,
    pub span: Span,
    pub fns: HashMap<String, u32>,
    pub assoc: HashMap<String, &'a ast::Ty>,
    pub trait_id: Option<u32>,
}

pub struct TraitInfo<'a> {
    pub module: u32,
    pub name: String,
    pub decl: &'a ast::TraitDecl,
    pub fns: HashMap<String, u32>,
    pub impls: Vec<u32>,
}

pub struct ConstInfo<'a> {
    pub module: u32,
    pub decl: &'a ast::ConstDecl,
    pub span: Span,
    pub value: Option<(mir::Const, TyId)>,
    pub busy: bool,
}

pub struct StaticInfo<'a> {
    pub module: u32,
    pub decl: &'a ast::ConstDecl,
    pub span: Span,
    /// Its type and first value, once needed.
    pub done: Option<(TyId, mir::Const)>,
}

pub struct AliasInfo<'a> {
    pub module: u32,
    pub ty: &'a ast::Ty,
}

/// The names a piece of code sees besides its module's: compile-time
/// parameters, `Self`.
#[derive(Clone, Debug, Default)]
pub struct Env {
    pub module: u32,
    pub names: Vec<(String, CVal)>,
    pub self_ty: Option<TyId>,
}

impl Env {
    pub fn get(&self, n: &str) -> Option<&CVal> {
        self.names.iter().rev().find(|(k, _)| k == n).map(|(_, v)| v)
    }
}

/// A function instance whose body is still to be lowered.
struct Pending {
    id: FnId,
    decl: u32,
    env: Env,
}

/// Where an instance came from, for error notes.
#[derive(Clone)]
pub struct InstInfo {
    pub decl: u32,
    pub env: Env,
}

#[derive(Default)]
pub struct Lang {
    pub drop: Option<u32>,
    pub clone: Option<u32>,
    pub option: Option<u32>,
    pub result: Option<u32>,
    pub string: Option<u32>,
    pub iterator: Option<u32>,
    pub eq: Option<u32>,
    pub ord: Option<u32>,
    pub hash: Option<u32>,
    pub show: Option<u32>,
}

pub struct Sema<'a> {
    pub ast: &'a Ast,
    pub types: Types,
    pub mods: Vec<ModScope>,
    pub adts: Vec<AdtDecl<'a>>,
    pub fns: Vec<FnDeclInfo<'a>>,
    pub impls: Vec<ImplInfo<'a>>,
    pub traits: Vec<TraitInfo<'a>>,
    pub consts: Vec<ConstInfo<'a>>,
    pub aliases: Vec<AliasInfo<'a>>,
    pub statics: Vec<StaticInfo<'a>>,
    /// Impls whose type is not a declared struct or enum (`impl str`).
    pub other_impls: Vec<u32>,
    adt_insts: HashMap<(u32, Vec<CVal>), TyId>,
    fn_insts: HashMap<(u32, Vec<CVal>), FnId>,
    impl_cache: HashMap<(u32, TyId), Option<(u32, Vec<CVal>)>>,
    pub out: Vec<mir::Function>,
    pub inst_info: Vec<Option<InstInfo>>,
    queue: VecDeque<Pending>,
    pub lang: Lang,
    pub freestanding: bool,
    pub target: crate::target::Target,
    pub checked: bool,
    lambda_count: u32,
    /// Instances being lowered, for "required by" notes.
    stack: Vec<FnId>,
    /// Compile-time closure parameters of instances being lowered: the
    /// instance, the name, its local, the closure's function.
    pub comptime_closures: Vec<(FnId, String, mir::Local, FnId)>,
    pub last_lambda: Option<(FnId, TyId)>,
    pub adt_args_of: HashMap<TyId, Vec<CVal>>,
}

pub fn ty_err<T>(span: Span, msg: &str) -> R<T> {
    Err(Diag::new(span, msg))
}

impl<'a> Sema<'a> {
    pub fn new(ast: &'a Ast, target: crate::target::Target, checked: bool) -> Sema<'a> {
        let root = &ast.modules[ast.root as usize];
        Sema {
            ast,
            types: Types::new(),
            mods: Vec::new(),
            adts: Vec::new(),
            fns: Vec::new(),
            impls: Vec::new(),
            traits: Vec::new(),
            consts: Vec::new(),
            aliases: Vec::new(),
            statics: Vec::new(),
            other_impls: Vec::new(),
            adt_insts: HashMap::new(),
            fn_insts: HashMap::new(),
            impl_cache: HashMap::new(),
            out: Vec::new(),
            inst_info: Vec::new(),
            queue: VecDeque::new(),
            lang: Lang::default(),
            freestanding: root.ast.attrs.iter().any(|a| a == "freestanding"),
            target,
            checked,
            lambda_count: 0,
            stack: Vec::new(),
            comptime_closures: Vec::new(),
            last_lambda: None,
            adt_args_of: HashMap::new(),
        }
    }

    // ---- collecting declarations ----

    pub fn collect(&mut self) -> R<()> {
        let ast = self.ast;
        for (mi, m) in ast.modules.iter().enumerate() {
            let mi = mi as u32;
            let mut scope = ModScope { names: HashMap::new(), globs: Vec::new() };
            if let Some(p) = ast.prelude {
                if p != mi {
                    scope.globs.push(p);
                }
            }
            for (alias, target, _public, span) in &m.imports {
                if scope.names.insert(alias.clone(), (Sym::Module(*target), false)).is_some() {
                    return ty_err(*span, &format!("`{}` is defined twice", alias));
                }
            }
            self.mods.push(scope);
            for item in &m.ast.items {
                self.collect_item(mi, item)?;
            }
        }
        // The prelude's `pub import`s put those modules' names in every scope.
        if let Some(p) = ast.prelude {
            let globs: Vec<u32> = ast.modules[p as usize].imports.iter().filter(|i| i.2).map(|i| i.1).collect();
            for (mi, s) in self.mods.iter_mut().enumerate() {
                if mi as u32 != p {
                    s.globs.extend(globs.iter().copied().filter(|&g| g != mi as u32));
                } else {
                    s.globs.extend(globs.iter().copied());
                }
            }
        }
        // Impls: attach to their type and trait.
        for i in 0..self.impls.len() {
            let ii = &self.impls[i];
            let module = ii.module;
            let decl = ii.decl;
            if let Some(tr) = &decl.trait_ {
                let t = self.resolve_trait(module, tr)?;
                self.impls[i].trait_id = Some(t);
                self.traits[t as usize].impls.push(i as u32);
            }
            let head = self.impl_head(module, &decl.self_ty, &decl.params);
            match head {
                Some(adt) if decl.trait_.is_none() => self.adts[adt as usize].impls.push(i as u32),
                _ if decl.trait_.is_none() => self.other_impls.push(i as u32),
                _ => {}
            }
        }
        for t in 0..self.traits.len() {
            let mut v = self.traits[t].impls.clone();
            v.sort_by_key(|&i| {
                let d = self.impls[i as usize].decl;
                matches!(&d.self_ty.kind, ast::TyKind::Path(p, None) if p.len() == 1 && d.params.iter().any(|q| q.name == p[0]))
            });
            self.traits[t].impls = v;
        }
        self.find_lang();
        Ok(())
    }

    fn find_lang(&mut self) {
        let Some(p) = self.ast.prelude else { return };
        let get = |s: &Self, n: &str| s.lookup(p, n);
        let trait_ = |s: &Self, n: &str| match get(s, n) {
            Some(Sym::Trait(t)) => Some(t),
            _ => None,
        };
        let adt = |s: &Self, n: &str| match get(s, n) {
            Some(Sym::Adt(t)) => Some(t),
            _ => None,
        };
        self.lang.drop = trait_(self, "Drop");
        self.lang.clone = trait_(self, "Clone");
        self.lang.iterator = trait_(self, "Iterator");
        self.lang.eq = trait_(self, "Eq");
        self.lang.ord = trait_(self, "Ord");
        self.lang.hash = trait_(self, "Hash");
        self.lang.show = trait_(self, "Show");
        self.lang.option = adt(self, "Option");
        self.lang.result = adt(self, "Result");
        self.lang.string = adt(self, "String");
    }

    /// The struct or enum an impl is for, when its type names one.
    fn impl_head(&self, module: u32, t: &ast::Ty, params: &[ast::Param]) -> Option<u32> {
        if let ast::TyKind::Path(p, _) = &t.kind {
            if p.len() == 1 && params.iter().any(|q| q.name == p[0]) {
                return None;
            }
            if let Some((Sym::Adt(a), _)) = self.lookup_path(module, p) {
                return Some(a);
            }
        }
        None
    }

    fn define(&mut self, module: u32, name: &str, sym: Sym, public: bool, span: Span) -> R<()> {
        if self.mods[module as usize].names.insert(name.to_string(), (sym, public)).is_some() {
            return ty_err(span, &format!("`{}` is defined twice", name));
        }
        Ok(())
    }

    fn collect_item(&mut self, module: u32, item: &'a ast::Item) -> R<()> {
        match &item.kind {
            ast::ItemKind::Import(_) => {}
            ast::ItemKind::Fn(f) => {
                let id = self.fns.len() as u32;
                self.fns.push(FnDeclInfo { module, decl: f, span: item.span, public: item.public, owner: Owner::Free });
                self.define(module, &f.name, Sym::Fn(id), item.public, f.name_span)?;
            }
            ast::ItemKind::Struct(s) => {
                let id = self.adts.len() as u32;
                self.adts.push(AdtDecl {
                    module,
                    name: s.name.clone(),
                    kind: AdtKind::Struct(s),
                    span: item.span,
                    derives: derives(item),
                    impls: Vec::new(),
                    is_view: item.attrs.iter().any(|a| a.name == "view"),
                });
                self.define(module, &s.name, Sym::Adt(id), item.public, item.span)?;
            }
            ast::ItemKind::Enum(e) => {
                let id = self.adts.len() as u32;
                self.adts.push(AdtDecl {
                    module,
                    name: e.name.clone(),
                    kind: AdtKind::Enum(e),
                    span: item.span,
                    derives: derives(item),
                    impls: Vec::new(),
                    is_view: item.attrs.iter().any(|a| a.name == "view"),
                });
                self.define(module, &e.name, Sym::Adt(id), item.public, item.span)?;
            }
            ast::ItemKind::Const(c) => {
                let id = self.consts.len() as u32;
                self.consts.push(ConstInfo { module, decl: c, span: item.span, value: None, busy: false });
                self.define(module, &c.name, Sym::Const(id), item.public, item.span)?;
            }
            ast::ItemKind::Static(c) => {
                let id = self.statics.len() as u32;
                self.statics.push(StaticInfo { module, decl: c, span: item.span, done: None });
                self.define(module, &c.name, Sym::Static(id), item.public, item.span)?;
            }
            ast::ItemKind::TypeAlias(name, Some(t)) => {
                let id = self.aliases.len() as u32;
                self.aliases.push(AliasInfo { module, ty: t });
                self.define(module, name, Sym::Alias(id), item.public, item.span)?;
            }
            ast::ItemKind::TypeAlias(_, None) => return ty_err(item.span, "a type alias needs `= type`"),
            ast::ItemKind::Trait(t) => {
                let id = self.traits.len() as u32;
                let mut fns = HashMap::new();
                for sub in &t.items {
                    match &sub.kind {
                        ast::ItemKind::Fn(f) => {
                            let fid = self.fns.len() as u32;
                            self.fns.push(FnDeclInfo { module, decl: f, span: sub.span, public: true, owner: Owner::Trait(id) });
                            fns.insert(f.name.clone(), fid);
                        }
                        ast::ItemKind::TypeAlias(_, _) => {}
                        _ => return ty_err(sub.span, "a trait holds functions and associated types"),
                    }
                }
                self.traits.push(TraitInfo { module, name: t.name.clone(), decl: t, fns, impls: Vec::new() });
                self.define(module, &t.name, Sym::Trait(id), item.public, item.span)?;
            }
            ast::ItemKind::Impl(im) => {
                let id = self.impls.len() as u32;
                let mut fns = HashMap::new();
                let mut assoc = HashMap::new();
                for sub in &im.items {
                    match &sub.kind {
                        ast::ItemKind::Fn(f) => {
                            let fid = self.fns.len() as u32;
                            self.fns.push(FnDeclInfo { module, decl: f, span: sub.span, public: sub.public || im.trait_.is_some(), owner: Owner::Impl(id) });
                            if fns.insert(f.name.clone(), fid).is_some() {
                                return ty_err(f.name_span, &format!("`{}` is defined twice in this impl", f.name));
                            }
                        }
                        ast::ItemKind::TypeAlias(n, Some(t)) => {
                            assoc.insert(n.clone(), t);
                        }
                        _ => return ty_err(sub.span, "an impl holds functions and associated types"),
                    }
                }
                self.impls.push(ImplInfo { module, decl: im, span: item.span, fns, assoc, trait_id: None });
            }
        }
        Ok(())
    }

    // ---- names ----

    pub fn lookup_in_module(&self, module: u32, name: &str, from_outside: bool) -> Option<(Sym, bool)> {
        if let Some(&(s, public)) = self.mods[module as usize].names.get(name) {
            if !from_outside || public {
                if from_outside && matches!(s, Sym::Module(_)) {
                    return None;
                }
                return Some((s, public));
            }
        }
        None
    }

    /// A name as seen from inside a module: its own items, then the globs.
    pub fn lookup(&self, module: u32, name: &str) -> Option<Sym> {
        if let Some(&(s, _)) = self.mods[module as usize].names.get(name) {
            return Some(s);
        }
        for &g in &self.mods[module as usize].globs {
            if let Some((s, _)) = self.lookup_in_module(g, name, true) {
                return Some(s);
            }
        }
        None
    }

    pub fn lookup_path(&self, module: u32, path: &[String]) -> Option<(Sym, u32)> {
        let mut s = self.lookup(module, &path[0])?;
        let mut m = module;
        for seg in &path[1..] {
            let Sym::Module(mm) = s else { return None };
            m = mm;
            s = self.lookup_in_module(mm, seg, true)?.0;
        }
        Some((s, m))
    }

    pub fn resolve_trait(&mut self, module: u32, t: &ast::Ty) -> R<u32> {
        if let ast::TyKind::Path(p, _) = &t.kind {
            if let Some((Sym::Trait(id), _)) = self.lookup_path(module, p) {
                return Ok(id);
            }
        }
        ty_err(t.span, "expected a trait")
    }

    /// Private items are seen by their own module, and the standard
    /// library's modules see each other's.
    pub fn same_package(&self, a: u32, b: u32) -> bool {
        a == b || (self.module_name(a).starts_with("std.") && self.module_name(b).starts_with("std."))
    }

    /// A static's type and first value (a constant, or zeroed).
    pub fn static_info(&mut self, id: u32) -> R<(TyId, mir::Const)> {
        if let Some(d) = &self.statics[id as usize].done {
            return Ok(d.clone());
        }
        let st = &self.statics[id as usize];
        let decl = st.decl;
        let env = Env { module: st.module, names: Vec::new(), self_ty: None };
        let Some(tyx) = &decl.ty else { return ty_err(st.span, "a static needs its type written") };
        let t = self.resolve_ty(tyx, &env)?;
        let c = match &decl.value.kind {
            ast::ExprKind::Call(f, args) if matches!(&f.kind, ast::ExprKind::Name(n) if n == "zeroed") && args.len() == 1 => mir::Const::Zeroed(t),
            _ => {
                let (c, ct) = self.const_expr(&decl.value, &env, Some(t))?;
                if ct != t {
                    return ty_err(decl.value.span, &format!("expected `{}`, found `{}`", self.types.show(t), self.types.show(ct)));
                }
                c
            }
        };
        self.statics[id as usize].done = Some((t, c.clone()));
        Ok((t, c))
    }

    pub fn module_name(&self, m: u32) -> &str {
        &self.ast.modules[m as usize].name
    }

    // ---- types ----

    pub fn builtin_ty(name: &str) -> Option<TyId> {
        Some(match name {
            "bool" => types::BOOL,
            "i8" => types::I8,
            "i16" => types::I16,
            "i32" => types::I32,
            "i64" | "int" => types::I64,
            "u8" => types::U8,
            "u16" => types::U16,
            "u32" => types::U32,
            "u64" => types::U64,
            "i128" => types::I128,
            "u128" => types::U128,
            "f32" => types::F32,
            "f64" => types::F64,
            "str" => types::STR,
            "type" => types::TYPE,
            "never" => types::NEVER,
            _ => return None,
        })
    }

    pub fn resolve_ty(&mut self, t: &ast::Ty, env: &Env) -> R<TyId> {
        match &t.kind {
            ast::TyKind::Path(p, args) => self.resolve_path_ty(p, args.as_deref(), env, t.span),
            ast::TyKind::Ptr(inner) => {
                let i = self.resolve_ty(inner, env)?;
                Ok(self.types.ptr(i))
            }
            ast::TyKind::Ref(inner, m) => {
                let i = self.resolve_ty(inner, env)?;
                Ok(if *m { self.types.refmut(i) } else { self.types.refty(i) })
            }
            ast::TyKind::Array(e, n) => {
                let et = self.resolve_ty(e, env)?;
                let n = self.const_int(n, env)?;
                if n < 0 {
                    return ty_err(t.span, "an array's length cannot be negative");
                }
                Ok(self.types.intern(TyKind::Array(et, n as u64)))
            }
            ast::TyKind::Slice(e) => {
                let et = self.resolve_ty(e, env)?;
                Ok(self.types.intern(TyKind::Slice(et)))
            }
            ast::TyKind::Tuple(ts) => {
                let mut v = Vec::new();
                for x in ts {
                    v.push(self.resolve_ty(x, env)?);
                }
                Ok(self.types.tuple(v))
            }
            ast::TyKind::Fn(ps, r) | ast::TyKind::FnPtr(ps, r) => {
                let mut params = Vec::new();
                for (m, x) in ps {
                    let pt = self.resolve_ty(x, env)?;
                    params.push(self.param_local_ty(*m, pt).0);
                }
                let ret = match r {
                    Some(r) => self.resolve_ty(r, env)?,
                    None => types::UNIT,
                };
                let sig = Sig { params, ret };
                Ok(self.types.intern(if matches!(t.kind, ast::TyKind::Fn(..)) { TyKind::Closure(sig) } else { TyKind::FnPtr(sig) }))
            }
        }
    }

    fn resolve_path_ty(&mut self, p: &[String], args: Option<&[ast::Expr]>, env: &Env, span: Span) -> R<TyId> {
        if p.len() == 1 && args.is_none() {
            if let Some(v) = env.get(&p[0]) {
                return match v {
                    CVal::Type(t) => Ok(*t),
                    _ => ty_err(span, &format!("`{}` is a value, not a type", p[0])),
                };
            }
            if p[0] == "Self" {
                return env.self_ty.ok_or_else(|| Diag::new(span, "`Self` is only defined in impls and traits"));
            }
            if let Some(t) = Self::builtin_ty(&p[0]) {
                if self.lookup(env.module, &p[0]).is_none() {
                    return Ok(t);
                }
            }
        }
        // `T.Item`, `Self.Item`: an associated type.
        if p.len() == 2 && args.is_none() {
            let base = if p[0] == "Self" {
                env.self_ty
            } else {
                match env.get(&p[0]) {
                    Some(CVal::Type(t)) => Some(*t),
                    _ => None,
                }
            };
            if let Some(b) = base {
                return self.assoc_ty(b, &p[1], span);
            }
        }
        let Some((sym, _)) = self.lookup_path(env.module, p) else {
            return ty_err(span, &format!("unknown type `{}`", p.join(".")));
        };
        match sym {
            Sym::Adt(a) => {
                let nparams = self.adts[a as usize].params().len();
                let given = args.map(|a| a.len()).unwrap_or(0);
                if nparams != given {
                    return ty_err(span, &format!("`{}` takes {} argument(s), {} given", p.join("."), nparams, given));
                }
                let mut cargs = Vec::new();
                if let Some(args) = args {
                    let params = self.adts[a as usize].params().to_vec();
                    let pm = self.adts[a as usize].module;
                    for (prm, arg) in params.iter().zip(args) {
                        cargs.push(self.comptime_arg(prm, pm, arg, env)?);
                    }
                }
                self.adt_instance(a, cargs, span)
            }
            Sym::Alias(i) => {
                let al = &self.aliases[i as usize];
                let e = Env { module: al.module, names: Vec::new(), self_ty: None };
                let t = al.ty;
                self.resolve_ty(t, &e)
            }
            _ => ty_err(span, &format!("`{}` is not a type", p.join("."))),
        }
    }

    /// Evaluates the argument for a compile-time parameter declared in
    /// module `pm`.
    pub fn comptime_arg(&mut self, prm: &ast::Param, pm: u32, arg: &ast::Expr, env: &Env) -> R<CVal> {
        if self.param_is_type(prm, pm) {
            Ok(CVal::Type(self.expr_ty(arg, env)?))
        } else {
            let pty = match &prm.ty {
                Some(t) => self.resolve_ty(t, &Env { module: pm, ..Default::default() })?,
                None => types::I64,
            };
            let (c, _) = self.const_expr(arg, env, Some(pty))?;
            Ok(match c {
                mir::Const::Int(v, _) => CVal::Int(v),
                mir::Const::Bool(b) => CVal::Bool(b),
                _ => return ty_err(arg.span, "a compile-time argument must be an integer, a bool or a type"),
            })
        }
    }

    /// `comptime T: type` and `comptime T: Ord` take types.
    pub fn param_is_type(&self, prm: &ast::Param, module: u32) -> bool {
        match &prm.ty {
            Some(ast::Ty { kind: ast::TyKind::Path(p, None), .. }) => {
                (p.len() == 1 && p[0] == "type") || matches!(self.lookup_path(module, p), Some((Sym::Trait(_), _)))
            }
            _ => false,
        }
    }

    /// Bounds of a type parameter: the traits named as its type and after.
    pub fn param_bounds(&mut self, prm: &ast::Param, module: u32) -> R<Vec<u32>> {
        let mut out = Vec::new();
        if let Some(t) = &prm.ty {
            if let ast::TyKind::Path(p, None) = &t.kind {
                if let Some((Sym::Trait(id), _)) = self.lookup_path(module, p) {
                    out.push(id);
                }
            }
        }
        for b in &prm.bounds {
            out.push(self.resolve_trait(module, b)?);
        }
        Ok(out)
    }

    /// A type written as an expression: `Vec(i64)`, `*u8`, `[i64; 4]`.
    pub fn expr_ty(&mut self, e: &ast::Expr, env: &Env) -> R<TyId> {
        match self.try_expr_ty(e, env)? {
            Some(t) => Ok(t),
            None => ty_err(e.span, "expected a type"),
        }
    }

    pub fn try_expr_ty(&mut self, e: &ast::Expr, env: &Env) -> R<Option<TyId>> {
        use ast::ExprKind as E;
        Ok(Some(match &e.kind {
            E::Type(t) => self.resolve_ty(t, env)?,
            E::Unit => types::UNIT,
            E::Name(_) | E::Field(..) => {
                let Some(p) = expr_path(e) else { return Ok(None) };
                if !self.path_is_type(&p, env) {
                    return Ok(None);
                }
                self.resolve_path_ty(&p, None, env, e.span)?
            }
            E::Call(callee, args) => {
                let Some(p) = expr_path(callee) else { return Ok(None) };
                match self.lookup_path(env.module, &p) {
                    Some((Sym::Adt(_), _)) if env.get(&p[0]).is_none() => self.resolve_path_ty(&p, Some(args), env, e.span)?,
                    _ => return Ok(None),
                }
            }
            E::Unary(ast::UnOp::Deref, inner) => {
                let Some(t) = self.try_expr_ty(inner, env)? else { return Ok(None) };
                self.types.ptr(t)
            }
            E::ArrayRepeat(el, n) => {
                let Some(t) = self.try_expr_ty(el, env)? else { return Ok(None) };
                let n = self.const_int(n, env)?;
                self.types.intern(TyKind::Array(t, n as u64))
            }
            E::Array(items) if items.len() == 1 => {
                let Some(t) = self.try_expr_ty(&items[0], env)? else { return Ok(None) };
                self.types.intern(TyKind::Slice(t))
            }
            E::Tuple(items) => {
                let mut v = Vec::new();
                for i in items {
                    let Some(t) = self.try_expr_ty(i, env)? else { return Ok(None) };
                    v.push(t);
                }
                self.types.tuple(v)
            }
            _ => return Ok(None),
        }))
    }

    /// Whether a path names a type (and not a value) in this environment.
    pub fn path_is_type(&self, p: &[String], env: &Env) -> bool {
        if p.len() == 1 {
            if let Some(v) = env.get(&p[0]) {
                return matches!(v, CVal::Type(_));
            }
            if p[0] == "Self" {
                return env.self_ty.is_some();
            }
            if Self::builtin_ty(&p[0]).is_some() && self.lookup(env.module, &p[0]).is_none() {
                return true;
            }
        }
        if p.len() == 2 && (p[0] == "Self" || matches!(env.get(&p[0]), Some(CVal::Type(_)))) {
            return true;
        }
        matches!(self.lookup_path(env.module, p), Some((Sym::Adt(_) | Sym::Alias(_), _)))
    }

    pub fn adt_instance(&mut self, decl: u32, args: Vec<CVal>, span: Span) -> R<TyId> {
        let key = (decl, args.clone());
        if let Some(&t) = self.adt_insts.get(&key) {
            return Ok(t);
        }
        let d = &self.adts[decl as usize];
        let module = d.module;
        let params = d.params().to_vec();
        let kind = d.kind;
        let mut name = d.name.clone();
        if module != self.ast.root && self.ast.prelude != Some(module) && !self.module_name(module).starts_with("std.") {
            name = format!("{}.{}", self.module_name(module), name);
        }
        if !args.is_empty() {
            let parts: Vec<String> = args.iter().map(|a| self.show_cval(a)).collect();
            name = format!("{}({})", name, parts.join(", "));
        }
        let t = self.types.new_adt(name, decl);
        self.adt_insts.insert(key, t);
        self.adt_args_of.insert(t, args.clone());
        let mut env = Env { module, names: Vec::new(), self_ty: Some(t) };
        for (p, a) in params.iter().zip(args.iter()) {
            env.names.push((p.name.clone(), a.clone()));
        }
        let body = match kind {
            AdtKind::Struct(s) => {
                let mut fs = Vec::new();
                for f in &s.fields {
                    let ft = self.resolve_ty(&f.ty, &env)?;
                    self.check_storable(ft, f.ty.span)?;
                    fs.push(FieldDef { name: f.name.clone(), ty: ft, public: f.public || module == self.ast.root });
                }
                AdtBody::Struct(fs)
            }
            AdtKind::Enum(e) => {
                let mut vs = Vec::new();
                for v in &e.variants {
                    let mut fs = Vec::new();
                    for f in &v.fields {
                        let ft = self.resolve_ty(f, &env)?;
                        self.check_storable(ft, f.span)?;
                        fs.push(ft);
                    }
                    vs.push(VariantDef { name: v.name.clone(), fields: fs });
                }
                AdtBody::Enum(vs)
            }
        };
        let TyKind::Adt(idx) = *self.types.kind(t) else { unreachable!() };
        self.types.adts[idx as usize].body = body;
        let marked = self.adts[decl as usize].derives.iter().any(|d| d == "view") || self.adts[decl as usize].is_view;
        let view_arg = args.iter().any(|a| matches!(a, CVal::Type(x) if self.types.is_view(*x)));
        self.types.adts[idx as usize].view = marked || view_arg;
        // A value's own type contains itself only through a pointer.
        if self.contains_inline(t, t) {
            return ty_err(span, &format!("`{}` contains itself; put the inner one in a `Box`", self.types.show(t)));
        }
        if let Some(dr) = self.lang.drop {
            if self.find_impl(dr, t)?.is_some() {
                self.types.adts[idx as usize].has_drop = true;
            }
        }
        self.types.reset_drop_cache();
        Ok(t)
    }

    fn contains_inline(&self, t: TyId, target: TyId) -> bool {
        let mut stack = vec![t];
        let mut seen = std::collections::HashSet::new();
        let mut first = true;
        while let Some(x) = stack.pop() {
            if !first && x == target {
                return true;
            }
            first = false;
            if !seen.insert(x) {
                continue;
            }
            match self.types.kind(x) {
                TyKind::Tuple(ts) => stack.extend(ts),
                TyKind::Array(e, _) => stack.push(*e),
                TyKind::Adt(i) => match &self.types.adts[*i as usize].body {
                    AdtBody::Struct(fs) => stack.extend(fs.iter().map(|f| f.ty)),
                    AdtBody::Enum(vs) => {
                        for v in vs {
                            stack.extend(&v.fields)
                        }
                    }
                    AdtBody::Pending => {}
                },
                _ => {}
            }
        }
        false
    }

    /// Types exist only while compiling, and cannot be stored.
    pub fn check_storable(&mut self, t: TyId, span: Span) -> R<()> {
        if self.types.kind(t) == &TyKind::Type {
            return ty_err(span, "types exist only while compiling and cannot be stored");
        }
        Ok(())
    }

    pub fn show_cval(&self, c: &CVal) -> String {
        match c {
            CVal::Type(t) => self.types.show(*t),
            CVal::Int(i) => i.to_string(),
            CVal::Bool(b) => b.to_string(),
            CVal::Lambda(f, _) => format!("closure#{}", f),
        }
    }

    pub fn assoc_ty(&mut self, base: TyId, name: &str, span: Span) -> R<TyId> {
        // Search every trait the type implements for an associated type of
        // that name.
        for tr in 0..self.traits.len() as u32 {
            let has = self.traits[tr as usize].decl.items.iter().any(|i| matches!(&i.kind, ast::ItemKind::TypeAlias(n, _) if n == name));
            if !has {
                continue;
            }
            if let Some((imp, args)) = self.find_impl(tr, base)? {
                if imp >= u32::MAX - 1 {
                    continue;
                }
                let ii = &self.impls[imp as usize];
                let Some(&t) = ii.assoc.get(name) else { continue };
                let env = self.impl_env(imp, &args, base);
                return self.resolve_ty(t, &env);
            }
        }
        ty_err(span, &format!("`{}` has no associated type `{}`", self.types.show(base), name))
    }

    pub fn impl_env(&self, imp: u32, args: &[CVal], self_ty: TyId) -> Env {
        let ii = &self.impls[imp as usize];
        let mut env = Env { module: ii.module, names: Vec::new(), self_ty: Some(self_ty) };
        for (p, a) in ii.decl.params.iter().zip(args) {
            env.names.push((p.name.clone(), a.clone()));
        }
        env
    }

    // ---- impls ----

    /// Matches an impl's type against a concrete type, binding the impl's
    /// parameters.
    pub fn match_impl(&mut self, imp: u32, t: TyId) -> R<Option<Vec<CVal>>> {
        let ii = &self.impls[imp as usize];
        let module = ii.module;
        let decl = ii.decl;
        let mut binds: Vec<Option<CVal>> = vec![None; decl.params.len()];
        if !self.match_ty(&decl.self_ty, t, &decl.params, module, &mut binds)? {
            return Ok(None);
        }
        let mut args = Vec::new();
        for (i, b) in binds.into_iter().enumerate() {
            match b {
                Some(v) => args.push(v),
                None => return ty_err(decl.params[i].span, "this impl parameter does not appear in the impl's type"),
            }
        }
        // Bounds on the parameters.
        for (p, a) in decl.params.iter().zip(&args) {
            if let CVal::Type(at) = a {
                for b in self.param_bounds(p, module)? {
                    if self.find_impl(b, *at)?.is_none() {
                        return Ok(None);
                    }
                }
            }
        }
        Ok(Some(args))
    }

    fn match_ty(&mut self, pat: &ast::Ty, t: TyId, params: &[ast::Param], module: u32, binds: &mut [Option<CVal>]) -> R<bool> {
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
            (A::Ptr(inner), TyKind::Ptr(x)) => self.match_ty(inner, *x, params, module, binds),
            (A::Ref(inner, false), TyKind::Ref(x)) | (A::Ref(inner, true), TyKind::RefMut(x)) => self.match_ty(inner, *x, params, module, binds),
            (A::Slice(inner), TyKind::Slice(x)) => self.match_ty(inner, *x, params, module, binds),
            (A::Array(inner, n), TyKind::Array(x, len)) => {
                if !self.match_ty(inner, *x, params, module, binds)? {
                    return Ok(false);
                }
                self.match_val(n, CVal::Int(*len as i128), params, module, binds)
            }
            (A::Tuple(ps), TyKind::Tuple(xs)) => {
                if ps.len() != xs.len() {
                    return Ok(false);
                }
                for (p, x) in ps.iter().zip(xs.clone()) {
                    if !self.match_ty(p, x, params, module, binds)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (A::Path(p, args), TyKind::Adt(i)) => {
                let decl = self.types.adts[*i as usize].decl;
                match self.lookup_path(module, p) {
                    Some((Sym::Adt(d), _)) if d == decl => {}
                    _ => return Ok(false),
                }
                let concrete: Vec<CVal> = self.adt_args_of.get(&t).cloned().unwrap_or_default();
                let args = args.as_deref().unwrap_or(&[]);
                if args.len() != concrete.len() {
                    return Ok(false);
                }
                for (a, c) in args.iter().zip(concrete) {
                    match c {
                        CVal::Type(ct) => {
                            let Some(at) = expr_as_ty(a) else { return Ok(false) };
                            if !self.match_ty(&at, ct, params, module, binds)? {
                                return Ok(false);
                            }
                        }
                        v => {
                            if !self.match_val(a, v, params, module, binds)? {
                                return Ok(false);
                            }
                        }
                    }
                }
                Ok(true)
            }
            _ => {
                let env = Env { module, names: Vec::new(), self_ty: None };
                match self.resolve_ty(pat, &env) {
                    Ok(pt) => Ok(pt == t),
                    Err(_) => Ok(false),
                }
            }
        }
    }

    fn match_val(&mut self, e: &ast::Expr, v: CVal, params: &[ast::Param], module: u32, binds: &mut [Option<CVal>]) -> R<bool> {
        if let ast::ExprKind::Name(n) = &e.kind {
            if let Some(i) = params.iter().position(|q| &q.name == n) {
                return Ok(match &binds[i] {
                    Some(old) => *old == v,
                    None => {
                        binds[i] = Some(v);
                        true
                    }
                });
            }
        }
        let env = Env { module, names: Vec::new(), self_ty: None };
        let (c, _) = self.const_expr(e, &env, None)?;
        Ok(match (c, v) {
            (mir::Const::Int(a, _), CVal::Int(b)) => a == b,
            (mir::Const::Bool(a), CVal::Bool(b)) => a == b,
            _ => false,
        })
    }

    /// The impl of a trait for a type, with the impl's arguments.
    pub fn find_impl(&mut self, tr: u32, t: TyId) -> R<Option<(u32, Vec<CVal>)>> {
        if let Some(r) = self.impl_cache.get(&(tr, t)) {
            return Ok(r.clone());
        }
        // Marker traits the compiler implements.
        if self.traits[tr as usize].module == self.ast.prelude.unwrap_or(u32::MAX) {
            let k = self.types.kind(t).clone();
            let builtin = match self.traits[tr as usize].name.as_str() {
                "Plain" => Some(self.types.is_plain(t) && !matches!(k, TyKind::Type)),
                "Int" => Some(matches!(k, TyKind::Int(_))),
                "Signed" => Some(matches!(k, TyKind::Int(i) if i.signed)),
                "Unsigned" => Some(matches!(k, TyKind::Int(i) if !i.signed)),
                "Float" => Some(matches!(k, TyKind::Float(_))),
                "Number" => Some(matches!(k, TyKind::Int(_) | TyKind::Float(_))),
                _ => None,
            };
            if let Some(b) = builtin {
                let r = if b { Some((u32::MAX - 1, Vec::new())) } else { None };
                self.impl_cache.insert((tr, t), r.clone());
                return Ok(r);
            }
        }
        self.impl_cache.insert((tr, t), None);
        let mut found = None;
        let impls = self.traits[tr as usize].impls.clone();
        for imp in impls {
            if let Some(args) = self.match_impl(imp, t)? {
                found = Some((imp, args));
                break;
            }
        }
        if found.is_none() {
            found = self.derived_impl(tr, t);
        }
        self.impl_cache.insert((tr, t), found.clone());
        Ok(found)
    }

    /// `#[derive(...)]` impls are written by the compiler; they are
    /// recorded as impl `u32::MAX`.
    fn derived_impl(&self, tr: u32, t: TyId) -> Option<(u32, Vec<CVal>)> {
        let adt = self.types.adt_of(t)?;
        let name = &self.traits[tr as usize].name;
        if self.adts[adt.decl as usize].derives.iter().any(|d| d == name) {
            Some((u32::MAX, Vec::new()))
        } else {
            None
        }
    }

    pub fn implements(&mut self, tr: u32, t: TyId) -> R<bool> {
        Ok(self.find_impl(tr, t)?.is_some())
    }

    /// A method by name: inherent impls first, then traits the type
    /// implements. Returns the function declaration and its impl arguments
    /// (for a trait's default body: `Self`).
    pub fn find_method(&mut self, t: TyId, name: &str) -> R<Option<(u32, Vec<CVal>)>> {
        let candidates: Vec<u32> = match self.types.adt_of(t) {
            Some(a) => self.adts[a.decl as usize].impls.clone(),
            None => self.other_impls.clone(),
        };
        for imp in candidates {
            let Some(&fid) = self.impls[imp as usize].fns.get(name) else { continue };
            if let Some(args) = self.match_impl(imp, t)? {
                return Ok(Some((fid, args)));
            }
        }
        for tr in 0..self.traits.len() as u32 {
            let Some(&default_fid) = self.traits[tr as usize].fns.get(name) else { continue };
            let Some((imp, args)) = self.find_impl(tr, t)? else { continue };
            if imp == u32::MAX - 1 {
                continue;
            }
            if imp != u32::MAX {
                if let Some(&fid) = self.impls[imp as usize].fns.get(name) {
                    return Ok(Some((fid, args)));
                }
            }
            return Ok(Some((default_fid, vec![CVal::Type(t)])));
        }
        Ok(None)
    }

    // ---- instances ----

    /// The environment of a function declaration given all its compile-time
    /// arguments: the impl's (or `Self` for a trait's) then its own.
    pub fn fn_env(&self, fid: u32, args: &[CVal]) -> (Env, usize) {
        let info = &self.fns[fid as usize];
        let mut env = Env { module: info.module, names: Vec::new(), self_ty: None };
        let mut used = 0;
        match info.owner {
            Owner::Free => {}
            Owner::Impl(imp) => {
                let ii = &self.impls[imp as usize];
                for p in &ii.decl.params {
                    env.names.push((p.name.clone(), args[used].clone()));
                    used += 1;
                }
            }
            Owner::Trait(_) => {
                if let Some(CVal::Type(t)) = args.first() {
                    env.self_ty = Some(*t);
                }
                used = 1;
            }
        }
        (env, used)
    }

    pub fn fn_self_ty(&mut self, fid: u32, env: &mut Env) -> R<()> {
        if let Owner::Impl(imp) = self.fns[fid as usize].owner {
            let t = self.impls[imp as usize].decl.self_ty.clone();
            let st = self.resolve_ty(&t, env)?;
            env.self_ty = Some(st);
        }
        Ok(())
    }

    /// The instance of a function for its compile-time arguments; its body
    /// is lowered later.
    pub fn instance(&mut self, fid: u32, args: Vec<CVal>, span: Span) -> R<FnId> {
        let key = (fid, args.clone());
        if let Some(&id) = self.fn_insts.get(&key) {
            return Ok(id);
        }
        if self.fn_insts.len() > 20000 {
            return ty_err(span, "too many instances of generic functions; does one instantiate itself forever?");
        }
        let (mut env, mut used) = self.fn_env(fid, &args);
        self.fn_self_ty(fid, &mut env)?;
        let info = &self.fns[fid as usize];
        let decl = info.decl;
        let module = info.module;
        for p in &decl.params {
            if p.mode == Mode::Comptime {
                let Some(a) = args.get(used) else { return ty_err(span, "missing compile-time argument") };
                env.names.push((p.name.clone(), a.clone()));
                used += 1;
            }
        }
        let mut params = Vec::new();
        let mut pass = Vec::new();
        for p in &decl.params {
            if p.mode == Mode::Comptime {
                // A closure argument still passes its environment.
                if let Some(CVal::Lambda(_, _)) = env.get(&p.name) {
                    let ct = self.resolve_ty(p.ty.as_ref().unwrap(), &env)?;
                    params.push(ct);
                    pass.push(ParamPass::Value);
                }
                continue;
            }
            let t = match &p.ty {
                Some(t) => self.resolve_ty(t, &env)?,
                None => env.self_ty.ok_or_else(|| Diag::new(p.span, "`self` outside an impl"))?,
            };
            let (lt, pp) = self.param_local_ty(p.mode, t);
            params.push(lt);
            pass.push(pp);
        }
        let ret_t = match &decl.ret {
            Some(t) => self.resolve_ty(t, &env)?,
            None => types::UNIT,
        };
        let ret = match decl.ret_mode {
            RetMode::Value => ret_t,
            RetMode::Ref => self.types.refty(ret_t),
            RetMode::Inout => self.types.refmut(ret_t),
        };
        let id = self.out.len() as FnId;
        let mname = self.module_name(module).to_string();
        let mut name = match self.fns[fid as usize].owner {
            Owner::Free => decl.name.clone(),
            _ => format!("{}.{}", env.self_ty.map(|t| self.types.show(t)).unwrap_or_default(), decl.name),
        };
        let own_cargs: Vec<String> = args.iter().skip(match self.fns[fid as usize].owner {
            Owner::Free => 0,
            Owner::Impl(imp) => self.impls[imp as usize].decl.params.len(),
            Owner::Trait(_) => 1,
        }).map(|a| self.show_cval(a)).collect();
        if !own_cargs.is_empty() {
            name = format!("{}({})", name, own_cargs.join(", "));
        }
        let (linkage, symbol) = match decl.kind {
            ast::FnKind::Extern => (Linkage::Extern, decl.name.clone()),
            ast::FnKind::Export => (Linkage::Export, decl.name.clone()),
            ast::FnKind::Normal => (Linkage::Internal, format!("{}.{}.{}", mname, sanitize(&name), id)),
        };
        if decl.kind != ast::FnKind::Normal && !args.is_empty() {
            return ty_err(decl.name_span, "extern and export functions cannot be generic");
        }
        self.out.push(mir::Function {
            symbol,
            name,
            sig: Sig { params, ret },
            pass,
            body: None,
            linkage,
            variadic: decl.variadic,
            returns_ref: decl.ret_mode != RetMode::Value,
            span: decl.name_span,
        });
        self.inst_info.push(Some(InstInfo { decl: fid, env: env.clone() }));
        self.fn_insts.insert(key, id);
        if decl.kind != ast::FnKind::Extern {
            if decl.body.is_none() {
                return ty_err(decl.name_span, "this function needs a body");
            }
            self.queue.push_back(Pending { id, decl: fid, env });
        }
        Ok(id)
    }

    /// How a parameter is held in the callee: by value, owned, or borrowed.
    pub fn param_local_ty(&mut self, mode: Mode, t: TyId) -> (TyId, ParamPass) {
        match mode {
            Mode::Let => {
                if self.types.is_scalar(t) || matches!(self.types.kind(t), TyKind::Str | TyKind::Slice(_) | TyKind::Closure(_)) {
                    (t, ParamPass::Value)
                } else {
                    (self.types.refty(t), ParamPass::Borrow)
                }
            }
            Mode::Inout => (self.types.refmut(t), ParamPass::Borrow),
            Mode::Sink => {
                if self.types.is_scalar(t) {
                    (t, ParamPass::Value)
                } else {
                    (t, ParamPass::Owned)
                }
            }
            Mode::Comptime => (t, ParamPass::Value),
        }
    }

    pub fn next_lambda(&mut self) -> u32 {
        self.lambda_count += 1;
        self.lambda_count
    }

    pub fn run(&mut self) -> R<()> {
        while let Some(p) = self.queue.pop_front() {
            self.stack.push(p.id);
            let r = self.lower_fn(p.id, p.decl, p.env);
            self.stack.pop();
            if let Err(d) = r {
                return Err(self.with_origin(d, p.id));
            }
        }
        Ok(())
    }

    fn with_origin(&self, mut d: Diag, id: FnId) -> Diag {
        if let Some(Some(info)) = self.inst_info.get(id as usize) {
            if !info.env.names.is_empty() {
                d = d.note(None, &format!("in the instance `{}`", self.out[id as usize].name));
            }
        }
        d
    }
}

fn derives(item: &ast::Item) -> Vec<String> {
    item.attrs.iter().filter(|a| a.name == "derive").flat_map(|a| a.args.clone()).collect()
}

pub fn sanitize(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' || c == '.' { c } else { '_' }).collect()
}

/// `a.b.c` as a path, if the expression is one.
pub fn expr_path(e: &ast::Expr) -> Option<Vec<String>> {
    match &e.kind {
        ast::ExprKind::Name(n) => Some(vec![n.clone()]),
        ast::ExprKind::Field(b, n) => {
            let mut p = expr_path(b)?;
            p.push(n.clone());
            Some(p)
        }
        _ => None,
    }
}

/// An expression read as a type pattern (in impl heads).
pub fn expr_as_ty(e: &ast::Expr) -> Option<ast::Ty> {
    use ast::ExprKind as E;
    let kind = match &e.kind {
        E::Type(t) => return Some(t.clone()),
        E::Name(_) | E::Field(..) => ast::TyKind::Path(expr_path(e)?, None),
        E::Call(c, args) => ast::TyKind::Path(expr_path(c)?, Some(args.clone())),
        E::Unary(ast::UnOp::Deref, i) => ast::TyKind::Ptr(Box::new(expr_as_ty(i)?)),
        E::ArrayRepeat(el, n) => ast::TyKind::Array(Box::new(expr_as_ty(el)?), n.clone()),
        E::Array(items) if items.len() == 1 => ast::TyKind::Slice(Box::new(expr_as_ty(&items[0])?)),
        E::Tuple(items) => ast::TyKind::Tuple(items.iter().map(expr_as_ty).collect::<Option<Vec<_>>>()?),
        E::Unit => ast::TyKind::Tuple(vec![]),
        _ => return None,
    };
    Some(ast::Ty { kind, span: e.span })
}

pub fn compile(ast: &Ast, target: crate::target::Target, checked: bool) -> R<mir::Program> {
    let mut s = Sema::new(ast, target, checked);
    s.collect()?;
    let root = ast.root;
    let entry = match s.lookup(root, "main") {
        Some(Sym::Fn(f)) if s.fns[f as usize].module == root => Some(s.instance(f, Vec::new(), Span::default())?),
        _ => None,
    };
    // Exported functions are compiled whether or not anything calls them,
    // and so is every function of the program that is not generic, so that
    // it is checked.
    for fid in 0..s.fns.len() as u32 {
        let info = &s.fns[fid as usize];
        let generic = info.decl.params.iter().any(|p| p.mode == Mode::Comptime)
            || match info.owner {
                Owner::Free => false,
                Owner::Impl(i) => !s.impls[i as usize].decl.params.is_empty(),
                Owner::Trait(_) => true,
            };
        let user = !s.module_name(info.module).starts_with("std.");
        if info.decl.kind == ast::FnKind::Export || (user && !generic && info.decl.kind == ast::FnKind::Normal) {
            s.instance(fid, Vec::new(), Span::default())?;
        }
    }
    s.run()?;
    // Destructors of every type that has one, until no new types appear.
    let mut drop_impls: HashMap<TyId, FnId> = HashMap::new();
    if let Some(dr) = s.lang.drop {
        loop {
            let mut new = false;
            for i in 0..s.types.adts.len() {
                if !s.types.adts[i].has_drop {
                    continue;
                }
                let t = s.types.intern(TyKind::Adt(i as u32));
                if drop_impls.contains_key(&t) {
                    continue;
                }
                let Some((imp, args)) = s.find_impl(dr, t)? else { continue };
                let Some(&fid) = s.impls[imp as usize].fns.get("drop") else {
                    return ty_err(s.impls[imp as usize].span, "a `Drop` impl needs `fn drop(inout self)`");
                };
                let id = s.instance(fid, args, Span::default())?;
                drop_impls.insert(t, id);
                new = true;
            }
            s.run()?;
            if !new {
                break;
            }
        }
    }
    if entry.is_none() {
        return ty_err(Span { file: ast.modules[root as usize].ast.file, lo: 0, hi: 0 }, "the program has no `main` function");
    }
    let mut statics = Vec::new();
    for (i, st) in s.statics.iter().enumerate() {
        if let Some((t, c)) = &st.done {
            statics.push((format!("{}.{}.static{}", s.module_name(st.module), st.decl.name, i), *t, c.clone()));
        } else {
            statics.push((String::new(), types::UNIT, mir::Const::Zst(types::UNIT)));
        }
    }
    Ok(mir::Program { fns: s.out, types: s.types, entry, freestanding: s.freestanding, checked, target, drop_impls, statics })
}
