// Loading a program: the root file and every module it imports, each parsed
// once. `import a.b` looks for `a/b.<target>.<profile>.jh`,
// `a/b.<profile>.jh`, `a/b.<target>.jh`, then `a/b.jh`, next to the
// importing file, then in each search directory. Every module also sees the
// prelude (`std/prelude.jh`).

use crate::ast;
use crate::diag::{Diag, Sources, Span};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

pub struct ModuleAst {
    /// The dotted name it was imported by (the root is `main`).
    pub name: String,
    pub path: PathBuf,
    pub ast: ast::Module,
    /// Imports: the name they bind, the module, whether `pub import` (the
    /// prelude's way of putting a module's names in every scope).
    pub imports: Vec<(String, u32, bool, Span)>,
}

pub struct Ast {
    pub modules: Vec<ModuleAst>,
    pub root: u32,
    pub prelude: Option<u32>,
}

pub struct Loader<'a> {
    pub search: Vec<PathBuf>,
    pub target: &'a str,
    /// `native` or `freestanding`.
    pub profile: &'static str,
    pub sources: &'a mut Sources,
    by_path: HashMap<PathBuf, u32>,
    modules: Vec<ModuleAst>,
}

pub fn default_search(extra: &[PathBuf]) -> Vec<PathBuf> {
    let mut s: Vec<PathBuf> = extra.to_vec();
    if let Ok(p) = std::env::var("JIHOO_PATH") {
        for d in p.split(':').filter(|d| !d.is_empty()) {
            s.push(PathBuf::from(d));
        }
    }
    // The checkout's (or the installed) standard library.
    if let Ok(exe) = std::env::current_exe() {
        for anc in exe.ancestors().skip(1) {
            let lib = anc.join("lib");
            if lib.join("std").join("prelude.jh").exists() {
                s.push(lib);
                break;
            }
            let share = anc.join("share").join("jihoo").join("lib");
            if share.join("std").join("prelude.jh").exists() {
                s.push(share);
                break;
            }
        }
    }
    let here = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    if here.join("std").join("prelude.jh").exists() {
        s.push(here);
    }
    s
}

pub fn load(root: &Path, search: Vec<PathBuf>, target: &str, sources: &mut Sources, no_prelude: bool) -> Result<Ast, Diag> {
    // The profile decides which files the standard library's modules come
    // from, so it is read from the root's attributes first.
    let text = std::fs::read(root).unwrap_or_default();
    let freestanding = String::from_utf8_lossy(&text).lines().take_while(|l| l.trim().is_empty() || l.trim_start().starts_with("//") || l.trim_start().starts_with("#!")).any(|l| l.trim() == "#![freestanding]");
    let profile = if freestanding { "freestanding" } else { "native" };
    let mut l = Loader { search, target, profile, sources, by_path: HashMap::new(), modules: Vec::new() };
    let root_idx = l.load_file(root.to_path_buf(), "main".to_string(), Span::default())?;
    let prelude = if no_prelude {
        None
    } else {
        match l.find(&["std".to_string(), "prelude".to_string()], root) {
            Some(p) => Some(l.load_file(p, "std.prelude".to_string(), Span::default())?),
            None => {
                return Err(Diag::new(Span::default(), "cannot find the standard library (std/prelude.jh); set JIHOO_PATH or pass -I"))
            }
        }
    };
    Ok(Ast { modules: l.modules, root: root_idx, prelude })
}

impl Loader<'_> {
    fn find(&self, path: &[String], from: &Path) -> Option<PathBuf> {
        let mut dirs: Vec<PathBuf> = Vec::new();
        if let Some(d) = from.parent() {
            dirs.push(d.to_path_buf());
        }
        dirs.extend(self.search.iter().cloned());
        let rel: PathBuf = path.iter().collect();
        for d in dirs {
            let base = d.join(&rel);
            // `a.x86_64.freestanding.jh`, `a.freestanding.jh`, `a.x86_64.jh`, `a.jh`
            for ext in [format!("{}.{}.jh", self.target, self.profile), format!("{}.jh", self.profile), format!("{}.jh", self.target), "jh".to_string()] {
                let p = base.with_extension(ext);
                if p.exists() {
                    return Some(p);
                }
            }
        }
        None
    }

    fn load_file(&mut self, path: PathBuf, name: String, at: Span) -> Result<u32, Diag> {
        let key = path.canonicalize().unwrap_or(path.clone());
        if let Some(&i) = self.by_path.get(&key) {
            return Ok(i);
        }
        let text = std::fs::read(&path).map_err(|e| Diag::new(at, &format!("cannot read {}: {}", path.display(), e)))?;
        let file = self.sources.add(path.display().to_string(), text.clone());
        let toks = crate::lex::lex(file, &text)?;
        let module = crate::parse::parse_module(file, toks)?;
        let idx = self.modules.len() as u32;
        self.by_path.insert(key, idx);
        let mut imports = Vec::new();
        let mut wanted = Vec::new();
        for it in &module.items {
            if let ast::ItemKind::Import(imp) = &it.kind {
                wanted.push((imp.clone(), it.public, it.span));
            }
        }
        self.modules.push(ModuleAst { name, path: path.clone(), ast: module, imports: Vec::new() });
        for (imp, public, span) in wanted {
            let Some(p) = self.find(&imp.path, &path) else {
                return Err(Diag::new(span, &format!("cannot find module `{}`", imp.path.join("."))));
            };
            let m = self.load_file(p, imp.path.join("."), span)?;
            let alias = imp.alias.clone().unwrap_or_else(|| imp.path.last().unwrap().clone());
            imports.push((alias, m, public, span));
        }
        self.modules[idx as usize].imports = imports;
        Ok(idx)
    }
}
