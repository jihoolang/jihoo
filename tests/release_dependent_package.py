#!/usr/bin/env python3
"""Smoke-test a raw installed/extracted Linux compiler outside the checkout.

    python3 tests/release_dependent_package.py /opt/jihoo/bin/jihoo
    python3 tests/release_dependent_package.py /opt/jihoo/bin/jihoo --native

The default only checks sources, with LLVM/linker paths deliberately unavailable.
--native additionally builds and executes on the host at O0/O2 using LLVM's
normal backend (JIHOO_LLVM/JIHOO_CC/JIHOO_LD may select installed tools).
It does not test cross-architecture execution or certify distribution runtimes.
No checkout files or libraries are copied into the consumer directory. Nix shell
wrappers are deliberately unsupported: pass the packaged ELF executable.
"""

import argparse
import os
from pathlib import Path
import platform
import shutil
import struct
import subprocess
import tempfile


# Self-contained consumers derived from examples/core_{nat,sized_list,range}.jh
# and tests/core_vec_extend.py; this script also works away from the checkout.
CASES = {
    'nat': (30, """// Imported structural induction establishes a runtime loop invariant's bound.
// Steps(c, k) says the count c can advance to the iteration count k.
// All trace constructors and induction proofs are erased. main returns 30.
#![dependent_core]
import dependent.nat

fn counted(n: u64, limit: u64) -> refine(fn(c) { nat.Steps(c, n) }) {
    fold(n, fn(k) { refine(fn(c) { nat.Steps(c, k) }) }, pack(0, nat.stationary(0)),
        fn(i, p, acc) {
            if_lt(i, limit, fn(q) {
                pack(witness(acc) + 1, nat.steps_add(witness(acc), i, 1, proof(acc)))
            }, pack(witness(acc), nat.successor(witness(acc), i, proof(acc))))
    })
}

export fn count(n: u64, limit: u64) -> u64 { witness(counted(n, limit)) }

export fn slot(limit: u64) -> i64 {
    let c = counted(4, limit)
    index([10, 20, 30, 40, 50], witness(c), nat.steps_bound(witness(c), 4, proof(c)))
}

fn main() -> i64 { slot(2) }
"""),
    'sized_list': (18, """// A runtime loop builds an owned list whose exact length remains in its type.
// Imported structural map proofs preserve that index. A caller checks i < n
// once, then reads the mapped list without measuring its length or checking
// the bound again. main returns 18.
#![dependent_core]
import dependent.sized_list

fn increment(x: i64) -> i64 { x + 1 }

export fn at(n: u64, i: u64, x: i64) -> i64 {
    let xs = sized_list.repeat(n, x)
    let ys = sized_list.map(n, xs, increment)
    if_lt(i, n, fn(p) { sized_list.nth(n, ys, i, p) }, -1)
}

export fn measured(n: u64, x: i64) -> u64 {
    let xs = sized_list.repeat(n, x)
    witness(sized_list.size(n, xs))
}

fn main() -> i64 { at(3, 2, 17) }
"""),
    'range': (30, """// An owned snapshot of a runtime-selected range, with imported offset evidence.
// The source stays borrowed and the result has exactly count elements.
// The example checks endpoints at runtime; additions retain overflow checks.
// main returns 30.
#![dependent_core]
import dependent.range

fn total(n: u64, xs: ref buffer(n)) -> i64 {
    fold(n, 0, fn(i, p, acc) { acc + index(xs, i, p) })
}

export fn selected(n: u64, offset: u64, count: u64, value: i64) -> i64 {
    let source = alloc(n, value)
    if_lt(offset, n + 1, fn(start) {
        if_lt(count, sub(n, offset, start) + 1, fn(fits) {
            let copied: buffer(count) = range.copy(n, source, offset, count,
                lt_add(count, sub(n, offset, start) + 1, offset, fits))
            total(count, copied)
        }, -1)
    }, -1)
}

fn main() -> i64 { selected(5, 1, 3, 10) }
"""),
    "vec_bulk": (42, """#![dependent_core]
import dependent.vec
import dependent.vec_bulk

fn total(v: ref vec.Vec) -> i64 {
    fold(vec.len(v), 0, fn(i, p, acc) { acc + vec.get(v, i, p) })
}
fn extended(cap: u64, n: u64, x: i64) -> i64 {
    var v = vec.with_capacity(cap)
    let empty = vec.clear(&v)
    let xs = alloc(n, x)
    let grown = vec_bulk.extend(&v, n, xs)
    let exact = transport(fn(k) { Eq(vec.len(v), k + n) }, empty, grown)
    total(v)
}
// Exercise both reallocation and reuse of spare capacity.
fn main() -> i64 { extended(1, 3, 7) + extended(8, 3, 7) }
"""),
}

BAD_PROOF = """#![dependent_core]
import dependent.nat
fn bad() -> Eq(1, 2) { nat.eq_trans(1, 1, 2, refl(1), refl(1)) }
fn main() -> i64 { 0 }
"""


def run(command, cwd, env, expected=0, diagnostic=None):
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            capture_output=True, timeout=120)
    if result.returncode != expected or (diagnostic and diagnostic not in result.stderr):
        raise RuntimeError(
            f"{command!r}: expected status {expected}, diagnostic {diagnostic!r}; "
            f"got {result.returncode}\n{result.stdout}\n{result.stderr}")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("compiler", type=Path)
    parser.add_argument("--native", action="store_true",
                        help="also build and run with LLVM on this Linux host")
    args = parser.parse_args()
    compiler = args.compiler.resolve(strict=True)
    # Reject source-tree compilers even if supplied through a symlink.
    for parent in compiler.parents:
        if (parent / "compiler/main.jh").is_file():
            parser.error("compiler must be installed/extracted outside a checkout")
    with compiler.open("rb") as stream:
        elf = stream.read(20)
    if len(elf) < 20 or elf[:6] != b"\x7fELF\x02\x01":
        parser.error("pass the raw Linux ELF compiler, not a shell wrapper")
    machine = struct.unpack_from("<H", elf, 18)[0]
    host_machine = {"x86_64": 62, "aarch64": 183, "arm64": 183}.get(platform.machine())
    if platform.system() != "Linux" or machine != host_machine:
        parser.error("this smoke test requires a compiler for the native Linux architecture")

    # Do not inherit checkout paths, alternate backends, or checking bypasses.
    environment = {k: v for k, v in os.environ.items() if not k.startswith("JIHOO_")}
    runtime = dict(environment)
    for key in ("JIHOO_LLVM", "JIHOO_CC", "JIHOO_LD"):
        if key in os.environ:
            runtime[key] = os.environ[key]
    # Ignore TMPDIR, which development shells may place inside a checkout.
    with tempfile.TemporaryDirectory(prefix="jihoo-dependent-package-", dir="/tmp") as tmp:
        work = Path(tmp)
        unavailable = str(work / "unavailable-tool")
        checking = {**environment, "JIHOO_LLVM": unavailable,
                    "JIHOO_CC": unavailable, "JIHOO_LD": unavailable}
        version = run([str(compiler), "--version"], work, checking).stdout.strip()
        print(f"{version}; Linux {platform.machine()}; compiler={compiler}", flush=True)
        for name, (_, source) in CASES.items():
            (work / f"{name}.jh").write_text(source)
            run([str(compiler), "check", f"{name}.jh"], work, checking)
        (work / "bad-proof.jh").write_text(BAD_PROOF)
        run([str(compiler), "check", "bad-proof.jh"], work, checking,
            expected=1, diagnostic="core: type mismatch")
        print("PASS backend-free: four consumers and bad-proof rejection; JIHOO_PATH unset", flush=True)

        # A separate binary-only installation must not recover libraries from
        # the caller's checkout, original install, or inherited JIHOO_PATH.
        bare = work / "without-library" / "bin" / "jihoo"
        bare.parent.mkdir(parents=True)
        shutil.copy2(compiler, bare)
        for name in CASES:
            module = "vec" if name == "vec_bulk" else name
            run([str(bare), "check", f"{name}.jh"], work, checking,
                expected=1, diagnostic=f"cannot find module `dependent.{module}`")
        # Also cover the loader's prelude diagnostic for an ordinary consumer.
        (work / "plain.jh").write_text("fn main() -> i64 { 0 }\n")
        run([str(bare), "check", "plain.jh"], work, checking,
            expected=1, diagnostic="cannot find the standard library (std/prelude.jh)")
        print("PASS missing bundle: four dependent imports and standard prelude rejected", flush=True)

        if args.native:
            for name, (expected, _) in CASES.items():
                for level in ("-O0", "-O2"):
                    binary = work / f"{name}{level}"
                    run([str(compiler), "build", f"{name}.jh", level,
                         "-o", str(binary)], work, runtime)
                    run([str(binary)], work, runtime, expected=expected)
            print(f"PASS LLVM native execution: four consumers at O0/O2 on {platform.machine()}")
        else:
            print("SKIP LLVM/native execution (enable with --native)")


if __name__ == "__main__":
    main()
