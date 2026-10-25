// The `jihoo` command.

use jihoo::diag::Sources;
use jihoo::target::Target;
use jihoo::{compile, emit_llvm, Options};
use std::path::{Path, PathBuf};
use std::process::{exit, Command};

const USAGE: &str = "usage:
  jihoo run <file.jh> [link inputs] [-- args]   compile and run a program
  jihoo build <file.jh> [-o out] [link inputs]  compile a program
  jihoo emit-mir <file.jh>                      print the compiler's MIR
  jihoo emit-llvm <file.jh> [-o out]            print LLVM IR
  jihoo emit-tokens <file.jh>                   print the tokens of one file
  jihoo emit-ast <file.jh>                      print the syntax tree of one file
  jihoo emit-program <file.jh>                  print every module a program loads

options:
  -O0 -O1 -O2 -O3   optimization (default -O2)
  --release         integer overflow wraps instead of trapping
  --target <t>      x86_64 or aarch64 (Linux)
  -I <dir>          also look for modules in <dir>
  -o <file>         output file
  --keep-ll         keep the LLVM IR next to the output";

fn main() {
    // The parser and sema recurse once per level of nesting, and a debug
    // build's frames are large: give them room for the deepest code the
    // parser accepts.
    let t = std::thread::Builder::new().stack_size(256 << 20).spawn(run).expect("thread");
    if t.join().is_err() {
        exit(101);
    }
}

fn run() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(cmd) = args.first().cloned() else {
        eprintln!("{}", USAGE);
        exit(2);
    };
    let mut file: Option<PathBuf> = None;
    let mut out: Option<PathBuf> = None;
    let mut opt = "-O2".to_string();
    let mut search = Vec::new();
    let mut target = Target::host();
    let mut checked = true;
    let mut link: Vec<String> = Vec::new();
    let mut prog_args: Vec<String> = Vec::new();
    let mut keep_ll = false;
    let mut i = 1;
    while i < args.len() {
        let a = &args[i];
        match a.as_str() {
            "--" => {
                prog_args = args[i + 1..].to_vec();
                break;
            }
            "-o" => {
                i += 1;
                out = args.get(i).map(PathBuf::from);
            }
            "-I" => {
                i += 1;
                if let Some(d) = args.get(i) {
                    search.push(PathBuf::from(d));
                }
            }
            "--target" => {
                i += 1;
                target = match args.get(i).and_then(|t| Target::parse(t)) {
                    Some(t) => t,
                    None => {
                        eprintln!("error: unknown target; use x86_64 or aarch64");
                        exit(2);
                    }
                };
            }
            "--release" => checked = false,
            "--keep-ll" => keep_ll = true,
            "-O0" | "-O1" | "-O2" | "-O3" => opt = a.clone(),
            "-h" | "--help" => {
                println!("{}", USAGE);
                return;
            }
            _ if a.ends_with(".jh") && file.is_none() => file = Some(PathBuf::from(a)),
            _ if a.starts_with('-') && !a.starts_with("-l") && !a.starts_with("-L") => {
                eprintln!("error: unknown option `{}`\n\n{}", a, USAGE);
                exit(2);
            }
            _ => link.push(a.clone()),
        }
        i += 1;
    }
    let Some(file) = file else {
        eprintln!("error: no source file\n\n{}", USAGE);
        exit(2);
    };
    if cmd == "emit-tokens" || cmd == "emit-ast" {
        emit_syntax(&file, cmd == "emit-ast");
        return;
    }
    let opts = Options { search, target, checked, no_prelude: false };
    let mut sources = Sources::default();
    if cmd == "emit-program" {
        match jihoo::load::load(&file, jihoo::load::default_search(&opts.search), target.name(), &mut sources, false) {
            Ok(ast) => print!("{}", jihoo::astdump::program(&ast)),
            Err(d) => {
                eprintln!("{}", sources.render(&d));
                exit(1);
            }
        }
        return;
    }
    let mut prog = match compile(&file, &opts, &mut sources) {
        Ok(p) => p,
        Err(d) => {
            eprintln!("{}", sources.render(&d));
            exit(1);
        }
    };
    match cmd.as_str() {
        "emit-mir" => {
            for f in &prog.fns {
                print!("{}", jihoo::mir::show_function(&prog, f));
            }
        }
        "emit-llvm" => {
            let ll = emit_llvm(&mut prog);
            match out {
                Some(o) => std::fs::write(o, ll).expect("write"),
                None => print!("{}", ll),
            }
        }
        "build" | "run" => {
            let freestanding = prog.freestanding;
            let ll = emit_llvm(&mut prog);
            let exe = match (&out, cmd.as_str()) {
                (Some(o), _) => o.clone(),
                (None, "build") => PathBuf::from(file.file_stem().unwrap()),
                (None, _) => std::env::temp_dir().join(format!("jihoo-run-{}", std::process::id())),
            };
            if let Err(e) = link_exe(&ll, &exe, &opt, target, freestanding, &link, keep_ll) {
                eprintln!("error: {}", e);
                exit(1);
            }
            if cmd == "run" {
                let status = Command::new(&exe).args(&prog_args).status();
                if out.is_none() {
                    let _ = std::fs::remove_file(&exe);
                }
                match status {
                    Ok(s) => {
                        use std::os::unix::process::ExitStatusExt;
                        if let Some(sig) = s.signal() {
                            exit(128 + sig);
                        }
                        exit(s.code().unwrap_or(1));
                    }
                    Err(e) => {
                        eprintln!("error: cannot run {}: {}", exe.display(), e);
                        exit(1);
                    }
                }
            }
        }
        _ => {
            eprintln!("error: unknown command `{}`\n\n{}", cmd, USAGE);
            exit(2);
        }
    }
}

fn link_exe(ll: &str, exe: &Path, opt: &str, target: Target, freestanding: bool, link: &[String], keep: bool) -> Result<(), String> {
    let ll_path = if keep { exe.with_extension("ll") } else { std::env::temp_dir().join(format!("jihoo-{}-{}.ll", std::process::id(), exe.file_name().unwrap().to_string_lossy())) };
    std::fs::write(&ll_path, ll).map_err(|e| format!("cannot write {}: {}", ll_path.display(), e))?;
    let cc = std::env::var("JIHOO_CC").unwrap_or_else(|_| "clang".into());
    let mut c = Command::new(&cc);
    c.arg(opt).arg("-w").arg("-target").arg(target.triple()).arg("-x").arg("ir").arg(&ll_path).arg("-x").arg("none");
    if freestanding {
        // sections per function, so that unused ones (the 128-bit helpers of
        // std.rt) are left out
        c.args(["-nostdlib", "-static", "-fuse-ld=lld", "-ffunction-sections", "-Wl,--gc-sections"]);
    }
    for l in link {
        c.arg(l);
    }
    if !freestanding {
        c.arg("-lm");
    }
    c.arg("-o").arg(exe);
    let o = c.output().map_err(|e| format!("cannot run {}: {} (set JIHOO_CC to clang)", cc, e))?;
    if !keep {
        let _ = std::fs::remove_file(&ll_path);
    }
    if !o.status.success() {
        let err = String::from_utf8_lossy(&o.stderr);
        let lines: Vec<&str> = err.lines().filter(|l| !l.contains("warning:")).collect();
        return Err(format!("{} failed:\n{}", cc, lines.join("\n")));
    }
    Ok(())
}

/// The tokens of one file, one per line: its byte range, whether a newline
/// came before it, and the token; or its syntax tree (`astdump.rs`). The
/// compiler written in jihoo prints the same, to compare.
fn emit_syntax(file: &Path, ast: bool) {
    use jihoo::lex::Tok;
    let mut sources = Sources::default();
    let text = match std::fs::read(file) {
        Ok(t) => t,
        Err(_) => {
            eprintln!("error: cannot read {}", file.display());
            exit(1);
        }
    };
    let id = sources.add(file.display().to_string(), text.clone());
    let toks = match jihoo::lex::lex(id, &text) {
        Ok(t) => t,
        Err(d) => {
            eprintln!("{}", sources.render(&d));
            exit(1);
        }
    };
    if ast {
        match jihoo::parse::parse_module(id, toks) {
            Ok(m) => print!("{}", jihoo::astdump::module(&m)),
            Err(d) => {
                eprintln!("{}", sources.render(&d));
                exit(1);
            }
        }
        return;
    }
    let mut out = String::new();
    for t in &toks {
        let what = match &t.tok {
            Tok::Ident(s) => format!("ident {}", s),
            Tok::Int(n) => format!("int {}", n),
            Tok::Float(f) => format!("float {}", f.to_bits()),
            Tok::Str(b) => format!("str {}", b.iter().map(|c| format!("{:02x}", c)).collect::<String>()),
            Tok::Char(c) => format!("char {}", c),
            Tok::Eof => "eof".to_string(),
            t => jihoo::parse::tok_text(t),
        };
        out.push_str(&format!("{} {} {} {}\n", t.span.lo, t.span.hi, t.nl_before as u8, what));
    }
    print!("{}", out);
}
