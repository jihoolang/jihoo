#!/usr/bin/env python3
"""Execute compiler/core.jh transforms and validate their actual graph snapshots.

Run from the repository in the jihoo + Lean development environment:
  python3 tests/core_transform_certificates.py --compiler out/jihoo

The driver is rebuilt on every invocation and imports this checkout's core.jh.
The Lean checker consumes the actual stdout, not a hand-maintained fixture.
This tests exporter/source/run association; it does not formally prove that
association. The compiler, exporter, JSON adapter and execution environment
remain trusted. Source hashes in the optional manifest are provenance only,
not proof that an artifact faithfully represents an execution. The pure Lean
validator's theorem is about decoded graphs, not Core.infer or program safety.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TAGS = {
    "var", "natural", "integer", "u64", "i64", "array", "lt", "eq", "pi",
    "lam", "app", "elements", "index", "refl", "zeroLe", "decide", "uadd", "usub",
}


def run(command, *, success=True, cwd=ROOT):
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=180)
    if (result.returncode == 0) != success:
        raise AssertionError(
            f"{shlex.join(map(str, command))}: status {result.returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def validate(checker, path, *, success=True):
    result = run([*checker, str(path)], success=success, cwd=ROOT / "proofs")
    if success:
        assert result.stdout.strip() == "graph certificate accepted", result.stdout
    else:
        assert result.returncode == 1, result
        assert result.stderr.startswith("graph certificate rejected: "), (
            f"missing rejection marker\nstdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rejected_snapshots(shift, substitute):
    """Corrupt real accepted snapshots; every mutation must fail closed."""
    def changed(source, field, value):
        altered = copy.deepcopy(source)
        altered[field] = value
        return altered

    for field, value in (
        ("schema", 2), ("operation", "rewrite"), ("amount", -1),
        ("cutoff", 1), ("depth", 0), ("depth", 129), ("input", len(shift["before"])),
        ("output", len(shift["after"])), ("output", 0), ("replacement", None),
        ("replacement", 1),
        ("amount", shift["amount"] + 1), ("operation", "substitute"),
        ("amount", 1.5), ("amount", "2"), ("amount", 2**63),
    ):
        yield f"metadata-{field}-{value}", changed(shift, field, value)
    yield "changed-replacement", changed(substitute, "replacement", 0)
    yield "replacement-after-only", changed(substitute, "replacement", len(substitute["before"]))
    yield "substitute-amount", changed(substitute, "amount", 1)
    # These mutations preserve graph shape, prefix, ranges and all metadata.
    # They target binder semantics rather than only the parser/graph guards.
    for name, old, new in (
        ("capture-free-replacement", 4, 0),
        ("capture-inside-replacement-lambda", 5, 1),
    ):
        bad = copy.deepcopy(substitute)
        position = next(i for i in range(len(bad["before"]), len(bad["after"]))
                        if bad["after"][i] == ["var", old])
        bad["after"][position] = ["var", new]
        yield name, bad
    bad = copy.deepcopy(shift)
    position = next(i for i in range(len(bad["before"]), len(bad["after"]))
                    if bad["after"][i][0] == "elements")
    variable_one = bad["before"].index(["var", 1])
    bad["after"][position][1][2] = variable_one
    yield "shift-changed-bound-variable", bad
    bad = copy.deepcopy(shift)
    bad["after"][bad["output"]][1] = False
    yield "changed-erased-binder", bad
    yield "missing-field", {key: value for key, value in shift.items() if key != "cutoff"}
    yield "unknown-field", dict(shift, unchecked=True)
    yield "after-truncated", changed(shift, "after", shift["before"][:-1])

    bad = copy.deepcopy(shift)
    bad["before"][0] = ["i64"]
    yield "before-not-prefix", bad
    bad = copy.deepcopy(shift)
    bad["after"][0] = ["i64"]
    yield "after-mutated-prefix", bad

    # Make all node mutations in both snapshots where needed so prefix checking
    # cannot hide an incomplete graph decoder. Unreachable nodes also matter.
    for name, node in (
        ("unknown-constructor", ["global", 0]),
        ("forward-reference", ["array", 1]),
        ("self-reference", ["array", 0]),
        ("out-of-range-reference", ["array", 2**32 - 1]),
        ("var-overflow", ["var", 2**32]),
        ("var-negative", ["var", -1]),
        ("natural-overflow", ["natural", 2**64]),
        ("natural-negative", ["natural", -1]),
        ("integer-underflow", ["integer", -(2**63) - 1]),
        ("integer-overflow", ["integer", 2**63]),
        ("extra-node-operand", ["u64", 0]),
        ("missing-node-operand", ["var"]),
        ("wrong-node-type", {"tag": "u64"}),
        ("universe-limit", ["universe", 33]),
        ("universe-u32-overflow", ["universe", 2**32]),
        ("universe-negative", ["universe", -1]),
        ("universe-missing-level", ["universe"]),
        ("prop-extra-operand", ["prop", 0]),
    ):
        bad = copy.deepcopy(shift)
        bad["before"][0] = node
        bad["after"][0] = node
        yield name, bad
    bad = copy.deepcopy(shift)
    position = next(i for i, node in enumerate(bad["before"]) if node[0] == "lam")
    bad["before"][position][1] = 0
    bad["after"][position][1] = 0
    yield "binder-flag-not-bool", bad
    bad = copy.deepcopy(shift)
    bad["after"].append(["global", 0])
    yield "unreachable-unsupported-node", bad
    for tag, node in (("prop", ["prop"]), ("universe", ["universe", 32])):
        bad = copy.deepcopy(shift)
        bad["after"].append(node)
        bad["output"] = len(bad["after"]) - 1
        yield f"selected-{tag}", bad
        bad = copy.deepcopy(shift)
        bad["after"].extend([node, ["array", len(bad["after"])]])
        bad["output"] = len(bad["after"]) - 1
        yield f"reachable-{tag}", bad
    bad = copy.deepcopy(shift)
    bad["after"].append(["universe", 33])
    yield "unreachable-universe-limit", bad
    bad = copy.deepcopy(shift)
    bad["after"].append(["array", len(bad["after"])])
    yield "unreachable-self-reference", bad
    bad = copy.deepcopy(shift)
    bad["after"].append(["elements", [0] * 4097])
    yield "child-vector-limit", bad

    # Resource guards apply even to otherwise valid shape-only certificates.
    for name, nodes in (
        ("node-limit", [["u64"] for _ in range(4097)]),
        ("depth-limit", [["u64"]] + [["array", i] for i in range(129)]),
        ("expansion-limit", [["u64"]] + [["app", i, i] for i in range(19)]),
    ):
        bad = copy.deepcopy(shift)
        bad.update(before=nodes, after=nodes, input=len(nodes) - 1,
                   output=len(nodes) - 1, amount=0)
        yield name, bad


def test(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    driver = output / "core-transform-snapshots"
    build = [*compiler, "build", "-O2", "-I", "compiler",
             "tests/core_transform_snapshots.jh", "-o", str(driver)]
    run(build)
    accepted = {}
    for fixture in ("mixed", "all", "var", "above", "closed", "inert-sorts"):
        for operation, amount in (("shift", 0), ("shift", 2), ("substitute", 0)):
            name = f"{fixture}-{operation}-{amount}"
            result = run([str(driver), operation, fixture, str(amount)])
            path = output / f"{name}.json"
            path.write_text(result.stdout)
            document = json.loads(result.stdout)
            assert document["after"][:len(document["before"])] == document["before"]
            if (operation == "shift" and amount == 0) or fixture == "closed":
                assert document["input"] == document["output"]
                assert document["before"] == document["after"]
            else:
                assert document["output"] != document["input"]
            validate(checker, path)
            accepted[name] = document
    mixed = accepted["mixed-substitute-0"]
    assert TAGS == {node[0] for node in mixed["before"]}
    assert {node[1] for node in mixed["before"] if node[0] in ("pi", "lam")} == {False, True}
    assert any(node == ["var", 5] for node in mixed["before"])
    assert len(mixed["after"]) > len(mixed["before"])

    sorts = accepted["inert-sorts-shift-2"]
    assert all(node in sorts["before"] for node in
               (["prop"], ["universe", 0], ["universe", 31], ["universe", 32]))
    assert sorts["before"][sorts["input"]] == ["var", 0]

    failures = 0
    for fixture in ("selected-prop", "selected-universe", "reachable-sort"):
        result = run([str(driver), "shift", fixture, "0"])
        path = output / f"reject-{fixture}.json"
        path.write_text(result.stdout)
        validate(checker, path, success=False)
        failures += 1
    for name, document in rejected_snapshots(accepted["mixed-shift-2"], mixed):
        path = output / f"reject-{name}.json"
        path.write_text(json.dumps(document, separators=(",", ":")) + "\n")
        validate(checker, path, success=False)
        failures += 1
    # Invalid JSON cannot be mistaken for an empty/default certificate, and
    # duplicate fields must not be silently overwritten by a parser's map.
    encoded = json.dumps(mixed)
    for name, text in (
        ("truncated", '{"schema":'),
        ("trailing", encoded + " null"),
        ("late-trailing", encoded + " " * 65536 + " null"),
        ("duplicate-field", encoded.replace('"schema": 1', '"schema": 1, "schema": 1')),
        ("exponent", encoded.replace('"amount": 0', '"amount": 0e0')),
        ("escaped-tag", encoded.replace('"u64"', '"u\\u003634"')),
        ("excessive-number", encoded.replace('"amount": 0', '"amount": ' + "1" * 1000)),
        ("excessive-nesting", "[" * 9 + "0" + "]" * 9),
    ):
        path = output / f"reject-json-{name}.json"
        path.write_text(text)
        validate(checker, path, success=False)
        failures += 1
    oversized = encoded.encode() + b" " * (8 * 1024 * 1024 + 1 - len(encoded))
    for name, payload in (("utf8", b"\xff"), ("file-limit", oversized)):
        path = output / f"reject-json-{name}.json"
        path.write_bytes(payload)
        validate(checker, path, success=False)
        failures += 1

    # This is an actual compiler result, not JSON tampering: the implementation
    # casts the shifted index back to u32. On a maximal index it wraps to zero;
    # mathematical renaming must reject that result. This open, untyped graph
    # is not an accepted program and is not evidence of infer unsoundness.
    overflow = run([str(driver), "shift", "overflow", "1"])
    overflow_path = output / "reject-actual-u32-shift-overflow.json"
    overflow_path.write_text(overflow.stdout)
    overflow_document = json.loads(overflow.stdout)
    assert overflow_document["before"][overflow_document["input"]] == ["var", 2**32 - 1]
    assert overflow_document["after"][overflow_document["output"]] == ["var", 0]
    validate(checker, overflow_path, success=False)
    failures += 1

    exporter_rejections = 0
    for operation, fixture, amount, message in (
        ("shift", "unsupported", "1", "unsupported constructor"),
        ("substitute", "unsupported", "0", "unsupported constructor"),
        ("shift", "invalid", "1", "invalid term reference"),
        ("shift", "universe-overflow", "0", "universe level exceeds transport bound"),
        ("shift", "mixed", "-1", "unsupported amount"),
        ("shift", "mixed", "4294967296", "unsupported amount"),
        ("substitute", "mixed", "1", "unsupported amount"),
    ):
        result = run([str(driver), operation, fixture, amount], success=False)
        assert not result.stdout, result.stdout
        assert message in result.stderr, result.stderr
        exporter_rejections += 1

    manifest = {
        "source_sha256": {path: digest(ROOT / path) for path in (
            "compiler/core.jh", "tests/core_transform_snapshots.jh",
            "tests/core_transform_certificates.py",
        )},
        "compiler_command": compiler,
        "build_command": build,
        "checker_command": checker,
        "accepted": list(accepted),
        "rejected_certificates": failures,
        "exporter_rejections": exporter_rejections,
        "trust_boundary": "Hashes record inputs, not exporter fidelity or execution correctness.",
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"core graph certificates: {len(accepted)} actual transform snapshots accepted; "
          f"{failures} malformed/tampered certificates and {exporter_rejections} "
          "unsupported/failed exports rejected")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", default=os.environ.get("JIHOO_COMPILER", "jihoo"),
                        help="compiler command used to rebuild the actual Core test driver")
    parser.add_argument("--checker", default="lake env lean --run CheckGraph.lean",
                        help="validator command, run with proofs/ as working directory")
    parser.add_argument("--output-dir", type=Path, help="retain snapshots and source provenance here")
    args = parser.parse_args()
    compiler = shlex.split(args.compiler)
    # Relative executable paths are relative to the checkout, even though the
    # validator runs from proofs/.
    if "/" in compiler[0]:
        compiler[0] = str((ROOT / compiler[0]).resolve())
    checker = shlex.split(args.checker)
    if args.output_dir:
        test(compiler, checker, args.output_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="jihoo-graph-certificates-") as temporary:
            test(compiler, checker, Path(temporary))


if __name__ == "__main__":
    main()
