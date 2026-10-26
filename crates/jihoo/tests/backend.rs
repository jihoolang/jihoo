//! Real C ABI and backend integration, also runnable with JIHOO_COMPILER=stage2.
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn compiler() -> Command {
    let mut c = Command::new(
        std::env::var_os("JIHOO_COMPILER").unwrap_or_else(|| env!("CARGO_BIN_EXE_jihoo").into()),
    );
    c.current_dir(root())
        .env("JIHOO_PATH", root().join("lib"))
        .env("JIHOO_BACKEND", "llvm");
    c
}

struct Temp(PathBuf);
impl Temp {
    fn new(name: &str) -> Self {
        let p = std::env::temp_dir().join(format!("jihoo-backend-{}-{}", std::process::id(), name));
        std::fs::create_dir_all(&p).unwrap();
        Self(p)
    }
    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn success(o: Output) -> Output {
    assert!(
        o.status.success(),
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    );
    o
}

#[test]
fn c_abi_at_every_optimization_level() {
    let t = Temp::new("c-abi");
    let src = std::fs::read_to_string(root().join("tests/run/ffi.jh")).unwrap();
    let expected: String = src
        .lines()
        .filter_map(|l| l.strip_prefix("//> "))
        .map(|s| format!("{}\n", s))
        .collect();
    for backend in ["llvm", "clang"] {
        for opt in ["-O0", "-O1", "-O2", "-O3"] {
            let exe = t.path("ffi");
            success(
                compiler()
                    .env("JIHOO_BACKEND", backend)
                    .args(["build", opt, "tests/run/ffi.jh", "tests/ffi/native.c", "-o"])
                    .arg(&exe)
                    .output()
                    .unwrap(),
            );
            let o = success(Command::new(exe).output().unwrap());
            assert_eq!(
                String::from_utf8_lossy(&o.stdout),
                expected,
                "{} {}",
                backend,
                opt
            );
        }
    }
}

#[test]
fn c_links_exported_jihoo_object_without_main() {
    let t = Temp::new("export");
    let object = t.path("exports.o");
    let exe = t.path("consumer");
    success(
        compiler()
            .args(["emit-obj", "--lib", "tests/ffi/export.jh", "-o"])
            .arg(&object)
            .output()
            .unwrap(),
    );
    let cc = std::env::var("JIHOO_CC").unwrap_or_else(|_| "cc".into());
    success(
        Command::new(&cc)
            .current_dir(root())
            .arg("tests/ffi/consumer.c")
            .arg(&object)
            .args(["-lm", "-ldl", "-o"])
            .arg(&exe)
            .output()
            .unwrap(),
    );
    assert_eq!(
        success(Command::new(exe).output().unwrap()).stdout,
        b"C called jihoo\n"
    );
    let shared = t.path("libexports.so");
    success(
        Command::new(cc)
            .arg("-shared")
            .arg(object)
            .args(["-lm", "-ldl", "-o"])
            .arg(&shared)
            .output()
            .unwrap(),
    );
    let o = success(
        compiler()
            .args(["run", "tests/ffi/dynamic.jh", "--"])
            .arg(shared)
            .output()
            .unwrap(),
    );
    assert_eq!(o.stdout, b"42\n");
}

#[test]
fn objects_cross_compile_without_a_c_compiler() {
    let t = Temp::new("cross");
    for (target, machine) in [("x86_64", 62u16), ("aarch64", 183)] {
        let object = t.path(target);
        success(
            compiler()
                .env("JIHOO_CC", "/no-such-c-compiler")
                .args([
                    "emit-obj",
                    "examples/freestanding.jh",
                    "--target",
                    target,
                    "-o",
                ])
                .arg(&object)
                .output()
                .unwrap(),
        );
        let bytes = std::fs::read(object).unwrap();
        assert_eq!(&bytes[..4], b"\x7fELF");
        assert_eq!(u16::from_le_bytes([bytes[18], bytes[19]]), machine);
    }
}

#[test]
fn missing_llvm_is_reported_without_falling_back() {
    let t = Temp::new("missing");
    let o = compiler()
        .env("JIHOO_LLVM", t.path("no-library.so"))
        .args(["build", "examples/hello.jh", "-o"])
        .arg(t.path("hello"))
        .output()
        .unwrap();
    assert!(!o.status.success());
    assert!(String::from_utf8_lossy(&o.stderr).contains("no-library.so"));
    assert!(!Path::new(&t.path("hello")).exists());
    success(
        compiler()
            .env("JIHOO_LLVM", "/no-library.so")
            .args(["emit-llvm", "examples/hello.jh"])
            .output()
            .unwrap(),
    );
}
