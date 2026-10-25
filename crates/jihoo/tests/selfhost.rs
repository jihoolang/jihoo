// The compiler written in jihoo (`compiler/`), against this one: builds it
// with this compiler, then runs both on every `.jh` file in the repository
// and compares what they print, errors and exit status included.
//
//   cargo test --test selfhost

use std::path::{Path, PathBuf};
use std::process::Command;

/// The commands both compilers have, which print what a pass makes. Each
/// pass ported to jihoo adds its own.
const COMMANDS: &[&[&str]] = &[&["emit-tokens"], &["emit-ast"]];

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

/// What a command prints, both streams, and how it exits.
fn run(exe: &Path, args: &[&str], file: &Path) -> String {
    let o = Command::new(exe).args(args).arg(file).current_dir(root()).output().unwrap();
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
    let mut failed = Vec::new();
    for f in &files {
        // Relative paths, so that error messages name the file the same way.
        let rel = f.strip_prefix(root()).unwrap_or(f);
        for cmd in COMMANDS {
            let want = run(&stage0, cmd, rel);
            let got = run(&stage1, cmd, rel);
            if want != got {
                failed.push(format!("{} {}:\n--- stage 0\n{}--- stage 1\n{}", cmd.join(" "), rel.display(), want, got));
            }
        }
    }
    let _ = std::fs::remove_file(&stage1);
    if !failed.is_empty() {
        let shown: Vec<&String> = failed.iter().take(3).collect();
        panic!("{} of {} files differ:\n{}", failed.len(), files.len(), shown.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n"));
    }
}
