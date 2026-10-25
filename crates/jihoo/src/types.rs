// Types, interned in one table and referred to by index, and their memory
// layout, which the code generator and the interpreter share.

use std::collections::HashMap;

pub type TyId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IntTy {
    pub signed: bool,
    pub bits: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sig {
    pub params: Vec<TyId>,
    pub ret: TyId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TyKind {
    Bool,
    Int(IntTy),
    Float(u32),
    /// The type of `return`, `break`, `panic(...)`: no value.
    Never,
    /// Tuples, including `()` (no parts).
    Tuple(Vec<TyId>),
    Ptr(TyId),
    Array(TyId, u64),
    /// `[T]`: a borrowed view, a pointer and a length.
    Slice(TyId),
    /// `str`: a borrowed view of bytes.
    Str,
    /// A struct or enum instance.
    Adt(u32),
    /// Borrows, which only the compiler writes: parameters, local borrows,
    /// projections.
    Ref(TyId),
    RefMut(TyId),
    /// `fn(A) -> R`: a borrowed closure, a code pointer and an environment.
    Closure(Sig),
    /// `fnptr(A) -> R`.
    FnPtr(Sig),
    /// The type of types, at compile time.
    Type,
}

#[derive(Clone, Debug)]
pub enum AdtBody {
    /// Not filled in yet (an instance being built).
    Pending,
    Struct(Vec<FieldDef>),
    Enum(Vec<VariantDef>),
}

#[derive(Clone, Debug)]
pub struct FieldDef {
    pub name: String,
    pub ty: TyId,
    pub public: bool,
}

#[derive(Clone, Debug)]
pub struct VariantDef {
    pub name: String,
    pub fields: Vec<TyId>,
}

#[derive(Clone, Debug)]
pub struct AdtDef {
    /// What error messages call it: `Vec(i64)`.
    pub name: String,
    /// The declaration: an index into sema's table of struct and enum
    /// declarations.
    pub decl: u32,
    pub body: AdtBody,
    /// Whether the type has a `Drop` impl (filled in by sema).
    pub has_drop: bool,
    /// Marked `#[view]`, or has a view as an argument: it may hold borrows.
    pub view: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub size: u64,
    pub align: u64,
}

#[derive(Clone, Debug)]
pub struct EnumLayout {
    pub tag_bits: u32,
    /// Offsets of each variant's fields.
    pub fields: Vec<Vec<u64>>,
}

pub struct Types {
    pub kinds: Vec<TyKind>,
    map: HashMap<TyKind, TyId>,
    pub adts: Vec<AdtDef>,
    layouts: HashMap<TyId, Layout>,
    pub ptr_size: u64,
    needs_drop: HashMap<TyId, bool>,
}

pub const BOOL: TyId = 0;
pub const UNIT: TyId = 1;
pub const NEVER: TyId = 2;
pub const I8: TyId = 3;
pub const I16: TyId = 4;
pub const I32: TyId = 5;
pub const I64: TyId = 6;
pub const U8: TyId = 7;
pub const U16: TyId = 8;
pub const U32: TyId = 9;
pub const U64: TyId = 10;
pub const F32: TyId = 11;
pub const F64: TyId = 12;
pub const STR: TyId = 13;
pub const TYPE: TyId = 14;

impl Types {
    pub fn new() -> Types {
        let mut t = Types {
            kinds: Vec::new(),
            map: HashMap::new(),
            adts: Vec::new(),
            layouts: HashMap::new(),
            ptr_size: 8,
            needs_drop: HashMap::new(),
        };
        let int = |signed, bits| TyKind::Int(IntTy { signed, bits });
        for k in [
            TyKind::Bool,
            TyKind::Tuple(vec![]),
            TyKind::Never,
            int(true, 8),
            int(true, 16),
            int(true, 32),
            int(true, 64),
            int(false, 8),
            int(false, 16),
            int(false, 32),
            int(false, 64),
            TyKind::Float(32),
            TyKind::Float(64),
            TyKind::Str,
            TyKind::Type,
        ] {
            t.intern(k);
        }
        t
    }

    pub fn intern(&mut self, k: TyKind) -> TyId {
        if let Some(&id) = self.map.get(&k) {
            return id;
        }
        let id = self.kinds.len() as TyId;
        self.kinds.push(k.clone());
        self.map.insert(k, id);
        id
    }

    pub fn kind(&self, t: TyId) -> &TyKind {
        &self.kinds[t as usize]
    }

    pub fn ptr(&mut self, t: TyId) -> TyId {
        self.intern(TyKind::Ptr(t))
    }
    pub fn refty(&mut self, t: TyId) -> TyId {
        self.intern(TyKind::Ref(t))
    }
    pub fn refmut(&mut self, t: TyId) -> TyId {
        self.intern(TyKind::RefMut(t))
    }
    pub fn tuple(&mut self, ts: Vec<TyId>) -> TyId {
        self.intern(TyKind::Tuple(ts))
    }

    pub fn new_adt(&mut self, name: String, decl: u32) -> TyId {
        let idx = self.adts.len() as u32;
        self.adts.push(AdtDef { name, decl, body: AdtBody::Pending, has_drop: false, view: false });
        self.intern(TyKind::Adt(idx))
    }

    pub fn adt_of(&self, t: TyId) -> Option<&AdtDef> {
        match self.kind(t) {
            TyKind::Adt(i) => Some(&self.adts[*i as usize]),
            _ => None,
        }
    }

    pub fn int(&self, t: TyId) -> Option<IntTy> {
        match self.kind(t) {
            TyKind::Int(i) => Some(*i),
            _ => None,
        }
    }

    pub fn is_int(&self, t: TyId) -> bool {
        matches!(self.kind(t), TyKind::Int(_))
    }
    pub fn is_float(&self, t: TyId) -> bool {
        matches!(self.kind(t), TyKind::Float(_))
    }
    pub fn is_ptr(&self, t: TyId) -> bool {
        matches!(self.kind(t), TyKind::Ptr(_))
    }
    pub fn is_ref(&self, t: TyId) -> bool {
        matches!(self.kind(t), TyKind::Ref(_) | TyKind::RefMut(_))
    }
    pub fn pointee(&self, t: TyId) -> Option<TyId> {
        match self.kind(t) {
            TyKind::Ptr(p) | TyKind::Ref(p) | TyKind::RefMut(p) => Some(*p),
            _ => None,
        }
    }

    /// A value kept in one register: numbers, pointers, borrows.
    pub fn is_scalar(&self, t: TyId) -> bool {
        matches!(
            self.kind(t),
            TyKind::Bool | TyKind::Int(_) | TyKind::Float(_) | TyKind::Ptr(_) | TyKind::Ref(_) | TyKind::RefMut(_) | TyKind::FnPtr(_)
        )
    }

    pub fn is_zst(&mut self, t: TyId) -> bool {
        self.layout(t).size == 0
    }

    /// Whether a value of this type must be dropped: it owns memory or has a
    /// `Drop` impl. Values that need no drop copy implicitly ("plain").
    pub fn needs_drop(&mut self, t: TyId) -> bool {
        if let Some(&b) = self.needs_drop.get(&t) {
            return b;
        }
        self.needs_drop.insert(t, false); // recursion through pointers stops here
        let b = match self.kind(t).clone() {
            TyKind::Tuple(ts) => ts.iter().any(|&x| self.needs_drop(x)),
            TyKind::Array(e, n) => n > 0 && self.needs_drop(e),
            TyKind::Adt(i) => {
                let def = self.adts[i as usize].clone();
                def.has_drop
                    || match &def.body {
                        AdtBody::Struct(fs) => fs.iter().any(|f| self.needs_drop(f.ty)),
                        AdtBody::Enum(vs) => vs.iter().any(|v| v.fields.iter().any(|&f| self.needs_drop(f))),
                        AdtBody::Pending => false,
                    }
            }
            _ => false,
        };
        self.needs_drop.insert(t, b);
        b
    }

    /// Views hold borrows: the checker follows what they borrow, and they
    /// live no longer than it.
    pub fn is_view(&self, t: TyId) -> bool {
        match self.kind(t) {
            TyKind::Str | TyKind::Slice(_) | TyKind::Ref(_) | TyKind::RefMut(_) | TyKind::Closure(_) => true,
            TyKind::Tuple(ts) => ts.iter().any(|&x| self.is_view(x)),
            TyKind::Array(e, _) => self.is_view(*e),
            TyKind::Adt(i) => {
                let d = &self.adts[*i as usize];
                d.view
                    || match &d.body {
                        AdtBody::Struct(fs) => fs.iter().any(|f| self.is_view(f.ty)),
                        AdtBody::Enum(vs) => vs.iter().any(|v| v.fields.iter().any(|&f| self.is_view(f))),
                        AdtBody::Pending => false,
                    }
            }
            _ => false,
        }
    }

    /// Holds an exclusive borrow somewhere, so it cannot be copied.
    pub fn has_refmut(&self, t: TyId) -> bool {
        match self.kind(t) {
            TyKind::RefMut(_) => true,
            TyKind::Tuple(ts) => ts.iter().any(|&x| self.has_refmut(x)),
            TyKind::Array(e, _) => self.has_refmut(*e),
            TyKind::Adt(i) => match &self.adts[*i as usize].body {
                AdtBody::Struct(fs) => fs.iter().any(|f| self.has_refmut(f.ty)),
                AdtBody::Enum(vs) => vs.iter().any(|v| v.fields.iter().any(|&f| self.has_refmut(f))),
                AdtBody::Pending => false,
            },
            _ => false,
        }
    }

    /// Plain values copy implicitly.
    pub fn is_plain(&mut self, t: TyId) -> bool {
        !self.has_refmut(t) && !self.needs_drop(t)
    }

    pub fn reset_drop_cache(&mut self) {
        self.needs_drop.clear();
    }

    pub fn layout(&mut self, t: TyId) -> Layout {
        if let Some(&l) = self.layouts.get(&t) {
            return l;
        }
        let p = self.ptr_size;
        let l = match self.kind(t).clone() {
            TyKind::Bool => Layout { size: 1, align: 1 },
            TyKind::Int(i) => Layout { size: (i.bits / 8) as u64, align: (i.bits / 8) as u64 },
            TyKind::Float(b) => Layout { size: (b / 8) as u64, align: (b / 8) as u64 },
            TyKind::Never | TyKind::Type => Layout { size: 0, align: 1 },
            TyKind::Ptr(_) | TyKind::Ref(_) | TyKind::RefMut(_) | TyKind::FnPtr(_) => Layout { size: p, align: p },
            TyKind::Slice(_) | TyKind::Str | TyKind::Closure(_) => Layout { size: 2 * p, align: p },
            TyKind::Tuple(ts) => {
                let (l, _) = self.struct_layout(&ts);
                l
            }
            TyKind::Array(e, n) => {
                let el = self.layout(e);
                Layout { size: el.size * n, align: el.align }
            }
            TyKind::Adt(i) => match self.adts[i as usize].body.clone() {
                AdtBody::Struct(fs) => {
                    let ts: Vec<TyId> = fs.iter().map(|f| f.ty).collect();
                    self.struct_layout(&ts).0
                }
                AdtBody::Enum(_) => {
                    let (l, _) = self.enum_layout(t);
                    l
                }
                AdtBody::Pending => panic!("layout of a type still being defined"),
            },
        };
        self.layouts.insert(t, l);
        l
    }

    /// Fields in declaration order, each at its natural alignment, as C does.
    pub fn struct_layout(&mut self, ts: &[TyId]) -> (Layout, Vec<u64>) {
        let mut off = 0u64;
        let mut align = 1u64;
        let mut offs = Vec::new();
        for &f in ts {
            let l = self.layout(f);
            off = round_up(off, l.align);
            offs.push(off);
            off += l.size;
            align = align.max(l.align);
        }
        (Layout { size: round_up(off, align), align }, offs)
    }

    pub fn field_offsets(&mut self, t: TyId) -> Vec<u64> {
        match self.kind(t).clone() {
            TyKind::Tuple(ts) => self.struct_layout(&ts).1,
            TyKind::Adt(i) => match self.adts[i as usize].body.clone() {
                AdtBody::Struct(fs) => {
                    let ts: Vec<TyId> = fs.iter().map(|f| f.ty).collect();
                    self.struct_layout(&ts).1
                }
                _ => vec![],
            },
            TyKind::Slice(_) | TyKind::Str | TyKind::Closure(_) => vec![0, self.ptr_size],
            _ => vec![],
        }
    }

    /// The fields' types, for tuples and structs.
    pub fn field_tys(&self, t: TyId) -> Vec<TyId> {
        match self.kind(t) {
            TyKind::Tuple(ts) => ts.clone(),
            TyKind::Adt(i) => match &self.adts[*i as usize].body {
                AdtBody::Struct(fs) => fs.iter().map(|f| f.ty).collect(),
                _ => vec![],
            },
            _ => vec![],
        }
    }

    pub fn variants(&self, t: TyId) -> Option<&Vec<VariantDef>> {
        match self.kind(t) {
            TyKind::Adt(i) => match &self.adts[*i as usize].body {
                AdtBody::Enum(vs) => Some(vs),
                _ => None,
            },
            _ => None,
        }
    }

    /// A tag at offset 0, then each variant's fields laid out as a struct
    /// after it.
    pub fn enum_layout(&mut self, t: TyId) -> (Layout, EnumLayout) {
        let vs = self.variants(t).cloned().unwrap_or_default();
        let tag_bits: u32 = if vs.len() <= 256 { 8 } else { 32 };
        let tag_size = (tag_bits / 8) as u64;
        let mut size = tag_size;
        let mut align = tag_size;
        let mut fields = Vec::new();
        for v in &vs {
            let mut off = tag_size;
            let mut offs = Vec::new();
            for &f in &v.fields {
                let l = self.layout(f);
                off = round_up(off, l.align);
                offs.push(off);
                off += l.size;
                align = align.max(l.align);
            }
            size = size.max(off);
            fields.push(offs);
        }
        (Layout { size: round_up(size, align), align }, EnumLayout { tag_bits, fields })
    }

    pub fn show(&self, t: TyId) -> String {
        match self.kind(t) {
            TyKind::Bool => "bool".into(),
            TyKind::Int(i) => format!("{}{}", if i.signed { "i" } else { "u" }, i.bits),
            TyKind::Float(b) => format!("f{}", b),
            TyKind::Never => "never".into(),
            TyKind::Tuple(ts) if ts.is_empty() => "()".into(),
            TyKind::Tuple(ts) => {
                let parts: Vec<String> = ts.iter().map(|&x| self.show(x)).collect();
                format!("({})", parts.join(", "))
            }
            TyKind::Ptr(p) => format!("*{}", self.show(*p)),
            TyKind::Array(e, n) => format!("[{}; {}]", self.show(*e), n),
            TyKind::Slice(e) => format!("[{}]", self.show(*e)),
            TyKind::Str => "str".into(),
            TyKind::Adt(i) => self.adts[*i as usize].name.clone(),
            TyKind::Ref(p) => format!("ref {}", self.show(*p)),
            TyKind::RefMut(p) => format!("inout {}", self.show(*p)),
            TyKind::Closure(s) => format!("fn({}){}", self.show_list(&s.params), self.show_ret(s.ret)),
            TyKind::FnPtr(s) => format!("fnptr({}){}", self.show_list(&s.params), self.show_ret(s.ret)),
            TyKind::Type => "type".into(),
        }
    }

    fn show_list(&self, ts: &[TyId]) -> String {
        ts.iter().map(|&x| self.show(x)).collect::<Vec<_>>().join(", ")
    }

    fn show_ret(&self, r: TyId) -> String {
        if r == UNIT {
            String::new()
        } else {
            format!(" -> {}", self.show(r))
        }
    }
}

impl Default for Types {
    fn default() -> Self {
        Self::new()
    }
}

pub fn round_up(x: u64, a: u64) -> u64 {
    if a <= 1 {
        x
    } else {
        x.div_ceil(a) * a
    }
}
