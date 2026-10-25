// Runs every program in tests/run and checks its output, and compiles every
// program in tests/fail and checks its error.
//
// In tests/run, `//> text` lines give the expected standard output in
// order, and `// exit: N` the exit status (default 0). In tests/fail,
// `// error: text` gives a part of the expected error message.
//
//   cargo test --test programs            all of them
//   JIHOO_TEST=name cargo test --test programs   the ones whose name has `name`

use std::path::{Path, PathBuf};
use std::process::Command;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn files(dir: &str) -> Vec<PathBuf> {
    let filter = std::env::var("JIHOO_TEST").ok();
    let mut v: Vec<PathBuf> = std::fs::read_dir(root().join(dir))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|e| e == "jh").unwrap_or(false))
        .filter(|p| filter.as_ref().map(|f| p.to_string_lossy().contains(f.as_str())).unwrap_or(true))
        .collect();
    v.sort();
    v
}

fn jihoo() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_jihoo"))
}

fn run_one(p: &Path) -> Result<(), String> {
    let src = std::fs::read_to_string(p).unwrap();
    let want: Vec<String> = src.lines().filter_map(|l| l.trim_start().strip_prefix("//>")).map(|l| l.strip_prefix(' ').unwrap_or(l).to_string()).collect();
    let code: i32 = src.lines().find_map(|l| l.trim_start().strip_prefix("// exit:")).map(|s| s.trim().parse().unwrap()).unwrap_or(0);
    let args: Vec<String> = src.lines().find_map(|l| l.trim_start().strip_prefix("// args:")).map(|s| s.split_whitespace().map(String::from).collect()).unwrap_or_default();
    let exe = std::env::temp_dir().join(format!("jihoo-test-{}-{}", std::process::id(), p.file_stem().unwrap().to_string_lossy()));
    let opt = std::env::var("JIHOO_TEST_OPT").unwrap_or_else(|_| "-O1".into());
    let o = Command::new(jihoo()).arg("build").arg(&opt).arg(p).arg("-o").arg(&exe).output().unwrap();
    if !o.status.success() {
        return Err(format!("does not compile:\n{}", String::from_utf8_lossy(&o.stderr)));
    }
    let r = Command::new(&exe).args(&args).output().unwrap();
    let _ = std::fs::remove_file(&exe);
    let out = String::from_utf8_lossy(&r.stdout);
    let got: Vec<&str> = out.lines().collect();
    use std::os::unix::process::ExitStatusExt;
    let status = r.status.code().unwrap_or_else(|| 128 + r.status.signal().unwrap_or(0));
    if got != want || status != code {
        return Err(format!(
            "expected (exit {}):\n{}\ngot (exit {}):\n{}\nstderr:\n{}",
            code,
            want.join("\n"),
            status,
            got.join("\n"),
            String::from_utf8_lossy(&r.stderr)
        ));
    }
    Ok(())
}

fn fail_one(p: &Path) -> Result<(), String> {
    let src = std::fs::read_to_string(p).unwrap();
    let want: Vec<&str> = src.lines().filter_map(|l| l.trim_start().strip_prefix("// error:")).map(|s| s.trim()).collect();
    if want.is_empty() {
        return Err("no `// error:` line".into());
    }
    let o = Command::new(jihoo()).arg("emit-mir").arg(p).output().unwrap();
    let err = String::from_utf8_lossy(&o.stderr);
    if o.status.success() {
        return Err("compiles, but should not".into());
    }
    for w in want {
        if !err.contains(w) {
            return Err(format!("the error does not say `{}`:\n{}", w, err));
        }
    }
    Ok(())
}

fn check_all(dir: &str, f: fn(&Path) -> Result<(), String>) {
    let fs = files(dir);
    let results: Vec<(PathBuf, Result<(), String>)> = std::thread::scope(|s| {
        let hs: Vec<_> = fs.chunks(fs.len().div_ceil(8).max(1)).map(|chunk| s.spawn(move || chunk.iter().map(|p| (p.clone(), f(p))).collect::<Vec<_>>())).collect();
        hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
    });
    let mut failed = 0;
    for (p, r) in &results {
        if let Err(e) = r {
            failed += 1;
            eprintln!("--- {}: {}", p.display(), e);
        }
    }
    assert!(failed == 0, "{} of {} programs in {} failed", failed, results.len(), dir);
}

#[test]
fn run() {
    check_all("tests/run", run_one);
}

#[test]
fn fail() {
    check_all("tests/fail", fail_one);
}
