// The compiler written in jihoo (`compiler/`), against this one: builds it
// with this compiler, then runs both on every `.jh` file in the repository
// and compares what they print, errors and exit status included.
//
//   cargo test --test selfhost

use std::path::{Path, PathBuf};
use std::process::Command;

/// The commands both compilers have, which print what a pass makes. Each
/// pass ported to jihoo adds its own. `emit-mir` runs twice: before
/// elaboration (`JIHOO_NO_ELAB`), which shows sema's differences alone, and
/// with drops elaborated and borrows checked.
type Cmd = (&'static [&'static str], bool);
const COMMANDS: &[Cmd] = &[(&["emit-tokens"], false), (&["emit-ast"], false), (&["emit-program"], false), (&["emit-mir"], true), (&["emit-mir"], false)];

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn jihoo_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.is_dir() {
            jihoo_files(&p, out);
        } else if p.extension().map(|e| e == "jh").unwrap_or(false) {
            out.push(p);
        }
    }
}

/// What a command prints, both streams, and how it exits. Both compilers
/// find the standard library through `JIHOO_PATH`, so they name its files
/// the same way. `no_elab` sets `JIHOO_NO_ELAB`.
fn run(exe: &Path, args: &[String], file: &Path, no_elab: bool) -> String {
    let lib = root().join("lib").canonicalize().unwrap();
    let mut c = Command::new(exe);
    c.args(args).arg(file).env("JIHOO_PATH", lib).env_remove("JIHOO_NO_ELAB").current_dir(root());
    if no_elab {
        c.env("JIHOO_NO_ELAB", "1");
    }
    let o = c.output().unwrap();
    format!("{}{}exit {:?}\n", String::from_utf8_lossy(&o.stdout), String::from_utf8_lossy(&o.stderr), o.status.code())
}

#[test]
fn self_hosted_compiler_agrees() {
    let stage0 = PathBuf::from(env!("CARGO_BIN_EXE_jihoo"));
    let stage1 = std::env::temp_dir().join(format!("jihoo-stage1-{}", std::process::id()));
    let o = Command::new(&stage0).arg("build").arg("-O1").arg(root().join("compiler/main.jh")).arg("-o").arg(&stage1).output().unwrap();
    assert!(o.status.success(), "compiler/main.jh does not compile:\n{}", String::from_utf8_lossy(&o.stderr));

    let mut files = Vec::new();
    for d in ["lib", "tests", "examples", "compiler"] {
        jihoo_files(&root().join(d), &mut files);
    }
    files.sort();
    // a root file that is not there
    files.push(root().join("tests/selfhost/load/nonexistent.jh"));
    let mut failed = Vec::new();
    for f in &files {
        // Relative paths, so that error messages name the file the same way.
        let rel = f.strip_prefix(root()).unwrap_or(f);
        // `// load-args: -I dir` adds options to `emit-program`
        let load_args: Vec<String> = std::fs::read_to_string(f)
            .ok()
            .and_then(|s| s.lines().find_map(|l| l.trim_start().strip_prefix("// load-args:").map(|a| a.split_whitespace().map(String::from).collect())))
            .unwrap_or_default();
        for &(cmd, no_elab) in COMMANDS {
            let mut args: Vec<String> = cmd.iter().map(|s| s.to_string()).collect();
            if cmd[0] == "emit-program" || cmd[0] == "emit-mir" {
                args.extend(load_args.iter().cloned());
            }
            let want = run(&stage0, &args, rel, no_elab);
            let got = run(&stage1, &args, rel, no_elab);
            if want != got {
                let env = if no_elab { "JIHOO_NO_ELAB=1 " } else { "" };
                failed.push(format!("{}{} {}:\n--- stage 0\n{}--- stage 1\n{}", env, cmd.join(" "), rel.display(), want, got));
            }
        }
    }
    let _ = std::fs::remove_file(&stage1);
    if !failed.is_empty() {
        let shown: Vec<&String> = failed.iter().take(3).collect();
        panic!("{} of {} files differ:\n{}", failed.len(), files.len(), shown.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n"));
    }
}
