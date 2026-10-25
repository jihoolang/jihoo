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

options:
  -O0 -O1 -O2 -O3   optimization (default -O2)
  --release         integer overflow wraps instead of trapping
  --target <t>      x86_64 or aarch64 (Linux)
  -I <dir>          also look for modules in <dir>
  -o <file>         output file
  --keep-ll         keep the LLVM IR next to the output";

fn main() {
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
    let opts = Options { search, target, checked, no_prelude: false };
    let mut sources = Sources::default();
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
        c.args(["-nostdlib", "-static", "-fuse-ld=lld"]);
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
