// The compiler written in jihoo (`compiler/`), against this one: builds it
// with this compiler (stage 1), then runs both on every `.jh` file in the
// repository and compares what they print, errors and exit status
// included; runs the test programs built by each; and builds the compiler
// with stage 1 (stage 2), which must write the same LLVM IR as stage 1.
//
//   cargo test --test selfhost

use std::path::{Path, PathBuf};
use std::process::Command;

/// The commands both compilers have, which print what a pass makes, with
/// whether to set `JIHOO_NO_ELAB`. `emit-mir` runs twice: before
/// elaboration, which shows sema's differences alone, and with drops
/// elaborated and borrows checked.
type Cmd = (&'static [&'static str], bool);
const COMMANDS: &[Cmd] = &[
    (&["emit-tokens"], false),
    (&["emit-ast"], false),
    (&["emit-program"], false),
    (&["emit-mir"], true),
    (&["emit-mir"], false),
    (&["emit-llvm"], false),
    (&["emit-llvm", "--target", "aarch64"], false),
];

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn stage0() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_jihoo"))
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

/// Every `.jh` file of the repository, and a root file that is not there.
fn all_files() -> Vec<PathBuf> {
    let mut files = Vec::new();
    for d in ["lib", "tests", "examples", "compiler"] {
        jihoo_files(&root().join(d), &mut files);
    }
    files.sort();
    files.push(root().join("tests/selfhost/load/nonexistent.jh"));
    files
}

/// `compiler/main.jh` built by `compiler`, at a path of its own.
fn build_compiler(compiler: &Path, name: &str) -> PathBuf {
    let out = std::env::temp_dir().join(format!("jihoo-{}-{}", name, std::process::id()));
    let lib = root().join("lib").canonicalize().unwrap();
    let o = Command::new(compiler).arg("build").arg("-O1").arg(root().join("compiler/main.jh")).arg("-o").arg(&out).env("JIHOO_PATH", lib).env_remove("JIHOO_NO_ELAB").output().unwrap();
    assert!(o.status.success(), "compiler/main.jh does not compile ({}):\n{}{}", name, String::from_utf8_lossy(&o.stdout), String::from_utf8_lossy(&o.stderr));
    out
}

/// What a command prints, both streams, and how it exits. Both compilers
/// find the standard library through `JIHOO_PATH`, so they name its files
/// the same way.
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

/// `// load-args: -I dir` in a file adds options to the commands that load
/// a program.
fn load_args(f: &Path) -> Vec<String> {
    std::fs::read_to_string(f)
        .ok()
        .and_then(|s| s.lines().find_map(|l| l.trim_start().strip_prefix("// load-args:").map(|a| a.split_whitespace().map(String::from).collect())))
        .unwrap_or_default()
}

fn report(failed: &[String], of: usize) {
    if !failed.is_empty() {
        let shown: Vec<&str> = failed.iter().take(3).map(|s| s.as_str()).collect();
        panic!("{} of {} differ:\n{}", failed.len(), of, shown.join("\n"));
    }
}

#[test]
fn self_hosted_compiler_agrees() {
    let stage0 = stage0();
    let stage1 = build_compiler(&stage0, "stage1");
    let files = all_files();
    let mut failed = Vec::new();
    for f in &files {
        // Relative paths, so that error messages name the file the same way.
        let rel = f.strip_prefix(root()).unwrap_or(f);
        let load_args = load_args(f);
        for &(cmd, no_elab) in COMMANDS {
            let mut args: Vec<String> = cmd.iter().map(|s| s.to_string()).collect();
            if cmd[0] != "emit-tokens" && cmd[0] != "emit-ast" {
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
    report(&failed, files.len());
}

/// The programs of `tests/run` and `examples`, built and run by stage 1,
/// do what they do built by stage 0.
#[test]
fn stage1_builds_programs() {
    let stage0 = stage0();
    let stage1 = build_compiler(&stage0, "stage1-run");
    let mut files = Vec::new();
    for d in ["tests/run", "examples"] {
        for e in std::fs::read_dir(root().join(d)).unwrap() {
            let p = e.unwrap().path();
            if p.extension().map(|e| e == "jh").unwrap_or(false) {
                files.push(p);
            }
        }
    }
    files.sort();
    let mut failed = Vec::new();
    for f in &files {
        let rel = f.strip_prefix(root()).unwrap_or(f);
        let src = std::fs::read_to_string(f).unwrap();
        let mut args = vec!["run".to_string(), "-O1".to_string()];
        if let Some(a) = src.lines().find_map(|l| l.trim_start().strip_prefix("// args:")) {
            args.push("--".to_string());
            args.extend(a.split_whitespace().map(String::from));
        }
        // `run` takes the file before `--`.
        let (before, after) = args.split_at(2);
        let mut a0: Vec<String> = before.to_vec();
        a0.push(rel.display().to_string());
        a0.extend(after.iter().cloned());
        let lib = root().join("lib").canonicalize().unwrap();
        let out = |exe: &Path| {
            let o = Command::new(exe).args(&a0).env("JIHOO_PATH", &lib).env_remove("JIHOO_NO_ELAB").current_dir(root()).output().unwrap();
            format!("{}exit {:?}\n", String::from_utf8_lossy(&o.stdout), o.status.code())
        };
        let want = out(&stage0);
        let got = out(&stage1);
        if want != got {
            failed.push(format!("run {}:\n--- stage 0\n{}--- stage 1\n{}", rel.display(), want, got));
        }
    }
    let _ = std::fs::remove_file(&stage1);
    report(&failed, files.len());
}

/// Stage 1 builds the compiler again (stage 2), which writes the same LLVM
/// IR as stage 1 for every file: the compiler in jihoo compiles itself.
#[test]
fn stage2_agrees_with_stage1() {
    let stage1 = build_compiler(&stage0(), "stage1-self");
    let stage2 = build_compiler(&stage1, "stage2");
    let files = all_files();
    let mut failed = Vec::new();
    for f in &files {
        let rel = f.strip_prefix(root()).unwrap_or(f);
        let mut args = vec!["emit-llvm".to_string()];
        args.extend(load_args(f));
        let want = run(&stage1, &args, rel, false);
        let got = run(&stage2, &args, rel, false);
        if want != got {
            failed.push(format!("emit-llvm {}:\n--- stage 1\n{}--- stage 2\n{}", rel.display(), want, got));
        }
    }
    let _ = std::fs::remove_file(&stage1);
    let _ = std::fs::remove_file(&stage2);
    report(&failed, files.len());
}

/// A failed link reports clang's messages, without its warnings, the same
/// way from both compilers.
#[test]
fn link_errors_agree() {
    let stage0 = stage0();
    let stage1 = build_compiler(&stage0, "stage1-link");
    let out = std::env::temp_dir().join(format!("jihoo-link-{}", std::process::id()));
    let lib = root().join("lib").canonicalize().unwrap();
    let run = |exe: &Path| {
        let o = Command::new(exe).arg("build").arg("examples/hello.jh").arg("no-such-input.o").arg("-o").arg(&out).env("JIHOO_PATH", &lib).current_dir(root()).output().unwrap();
        (String::from_utf8_lossy(&o.stderr).to_string(), o.status.code())
    };
    let want = run(&stage0);
    let got = run(&stage1);
    let _ = std::fs::remove_file(&stage1);
    assert!(want.0.contains("failed:\n") && want.0.contains("no-such-input.o"), "stage 0 says:\n{}", want.0);
    assert_eq!(want, got);
}
