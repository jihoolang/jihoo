#!/usr/bin/env python3
"""Validate once-retained canonical artifacts, then replay on their actual Core graphs.

The initial JSON snapshot adapter remains unproved. Every replay handoff uses the
canonical codec instead: input files are read once, their retained bytes are sent
to Lean and to the reconstructed-Core consumer, and exact graph/root continuity
is checked before publishing a subsequent artifact. No source hash substitutes
for this identity check. Python orchestration, IO, compilation and the Jihoo
importer/invocation are a tested trusted boundary, not a lowering-safety theorem.
"""
from __future__ import annotations

import argparse
import copy
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def command(argv, payload=None, *, cwd=ROOT):
    return subprocess.run(argv, input=payload, capture_output=True, cwd=cwd, timeout=180)


def require(result):
    assert result.returncode == 0, (result.args, result.returncode,
                                    result.stdout.decode(errors="replace"),
                                    result.stderr.decode(errors="replace"))
    return result.stdout


def canonical_tokens(values):
    # Test mutation helper only. Positive replay artifacts always come from Lean
    # or the actual Jihoo consumer, never this independent Python serializer.
    return "".join((bin(n)[2:][::-1] if n else "") + ";" for n in values).encode()


def inspect(payload):
    """Independent test-only observations; not the production handoff validator."""
    assert payload.endswith(b";") and set(payload) <= set(b"01;")
    tokens = [int(part[::-1], 2) if part else 0 for part in payload[:-1].split(b";")]
    schema, root, output, operation, argument = tokens[:5]
    assert schema == 1
    index = 5

    def graph():
        nonlocal index
        count = tokens[index]
        index += 1
        nodes = []
        sizes = {0: 1, 1: 1, 2: 2, 3: 0, 4: 0, 5: 1, 6: 2, 7: 2,
                 8: 3, 9: 3, 10: 2, 12: 3, 13: 1, 14: 1, 15: 2, 16: 2, 17: 3, 18: 0, 19: 1}
        for _ in range(count):
            tag = tokens[index]
            index += 1
            size = sizes[tag] if tag != 11 else tokens[index] + 1
            nodes.append((tag, *tokens[index:index + size]))
            index += size
        return nodes

    before, after = graph(), graph()
    assert index == len(tokens)
    return dict(input=root, output=output, operation=operation, payload=argument,
                before=before, after=after)


class Replay:
    def __init__(self, checker, driver):
        self.checker = checker
        self.driver = driver
        self.validated = 0

    def lean(self, payload, *flags):
        return command([*self.checker, *flags], payload, cwd=ROOT / "proofs")

    def seed(self, document):
        result = self.lean(json.dumps(document).encode(), "--json-input")
        artifact = require(result)
        require(self.lean(artifact))
        return artifact

    def consume(self, prior, operation, amount=0, replacement=0):
        return command([str(self.driver), operation, str(amount), str(replacement)], prior)

    def checked(self, retained, operation, amount=0, replacement=0, *, consumer=None):
        # The caller reads an input artifact once. No file path is passed to a
        # checker or consumer: both receive this very same immutable byte string.
        require(self.lean(retained))
        invoke = self.consume if consumer is None else consumer
        result = require(invoke(retained, operation, amount, replacement))
        expected = (0, amount) if operation == "shift" else (1, replacement)
        observed = inspect(result)
        assert (observed["operation"], observed["payload"]) == expected, "operation mismatch"
        # The theorem-backed checker compares complete graphs and roots, not
        # merely hashes or equality of their decoded expressions.
        require(self.lean(retained + b"\n" + result, "--chain", operation, str(expected[1])))
        self.validated += 1
        return result


def test(compiler, checker, output):
    output.mkdir(parents=True, exist_ok=True)
    snapshot = output / "core-transform-snapshots"
    driver = output / "core-artifact-replay"
    for source, binary in (("core_transform_snapshots", snapshot), ("core_artifact_replay", driver)):
        require(command([*compiler, "build", "-O2", "-I", "compiler",
                         f"tests/{source}.jh", "-o", str(binary)]))
    replay = Replay(checker, driver)
    seeds, documents = {}, {}
    for fixture in ("mixed", "all", "var", "above", "closed", "inert-sorts"):
        raw = require(command([str(snapshot), "shift", fixture, "0"]))
        document = json.loads(raw)
        documents[fixture] = document
        seeds[fixture] = replay.seed(document)
        path = output / f"{fixture}-seed.artifact"
        path.write_bytes(seeds[fixture])
        # A single filesystem read supplies every consumer of this artifact.
        retained = path.read_bytes()
        if fixture == "inert-sorts":
            assert all(node in inspect(retained)["before"] for node in
                       ((18,), (19, 0), (19, 31), (19, 32)))
        for step, (operation, amount, replacement) in enumerate((
            ("shift", 2, 0), ("substitute", 0, 14), ("shift", 0, 0), ("shift", 1, 0),
        )):
            before = inspect(retained)
            result = replay.checked(retained, operation, amount, replacement)
            after = inspect(result)
            assert before["after"] == after["before"]
            assert before["output"] == after["input"]
            if operation == "shift" and amount == 0:
                assert after["before"] == after["after"]
                assert after["input"] == after["output"]
            (output / f"{fixture}-{step}-{operation}.artifact").write_bytes(result)
            retained = result
        if fixture == "mixed":
            assert len(inspect(retained)["after"]) > len(inspect(seeds[fixture])["after"])

    # Replacing the source path after the one read cannot switch the checked or
    # consumed bytes. No checker/consumer ever receives this mutable pathname.
    replacement_path = output / "retained-once.artifact"
    replacement_path.write_bytes(seeds["mixed"])
    retained = replacement_path.read_bytes()
    replacement_path.write_bytes(seeds["all"])
    result = replay.checked(retained, "shift", 1)
    assert inspect(result)["before"] == inspect(seeds["mixed"])["after"]

    rejected = 0

    def rejects_handoff(name, prior, operation, amount=0, replacement=0, *, consumer):
        nonlocal rejected
        # Prove this is a continuity/request rejection, not an importer crash,
        # malformed output or an independently invalid certificate.
        require(replay.lean(prior))
        produced = consumer(prior, operation, amount, replacement)
        response = require(produced)
        require(replay.lean(response))
        argument = amount if operation == "shift" else replacement
        checked = replay.lean(prior + b"\n" + response, "--chain", operation, str(argument))
        assert checked.returncode == 1 and b"rejected" in checked.stderr, (name, checked)
        try:
            replay.checked(prior, operation, amount, replacement,
                           consumer=lambda *_: produced)
        except AssertionError:
            rejected += 1
        else:
            raise AssertionError(f"accepted invalid handoff: {name}")

    # Valid but substituted input artifact: the consumer honestly transforms a
    # different graph, and each certificate alone validates. Only the exact
    # chain equality catches this. It is not a bad-hash test.
    alternate = seeds["all"]
    require(replay.lean(alternate))
    rejects_handoff("substituted-artifact", seeds["mixed"], "shift", 1,
                    consumer=lambda _, op, amount, replacement:
                        replay.consume(alternate, op, amount, replacement))
    # Same complete graph with a different valid output root must also fail.
    wrong_root = copy.deepcopy(documents["mixed"])
    wrong_root.update(input=0, output=0)
    root_artifact = replay.seed(wrong_root)
    assert inspect(root_artifact)["after"] == inspect(seeds["mixed"])["after"]
    rejects_handoff("wrong-intermediate-root", seeds["mixed"], "shift", 0,
                    consumer=lambda _, op, amount, replacement:
                        replay.consume(root_artifact, op, amount, replacement))
    # An unreachable node differs while the selected root/decoded term stay the
    # same. Whole-graph identity is deliberately stronger than semantic equality.
    different_graph = copy.deepcopy(documents["closed"])
    different_graph["before"][0] = ["i64"]
    different_graph["after"][0] = ["i64"]
    graph_artifact = replay.seed(different_graph)
    rejects_handoff("wrong-intermediate-graph", seeds["closed"], "shift", 0,
                    consumer=lambda _, op, amount, replacement:
                        replay.consume(graph_artifact, op, amount, replacement))
    # A valid response for a different requested operation, amount or replacement
    # must not be laundered merely because its mathematical relation is valid.
    for label, requested, actual in (
        ("operation", ("shift", 0, 0), ("substitute", 0, 14)),
        ("amount", ("shift", 1, 0), ("shift", 2, 0)),
        ("replacement", ("substitute", 0, 14), ("substitute", 0, 0)),
    ):
        # A closed root makes all these operations return the identical graph
        # and root. Continuity alone accepts; only requested metadata rejects.
        metadata_seed = seeds["closed"]
        response = require(replay.consume(metadata_seed, *actual))
        require(replay.lean(response))
        assert inspect(response)["before"] == inspect(response)["after"]
        require(replay.lean(metadata_seed + b"\n" + response, "--chain"))
        argument = requested[1] if requested[0] == "shift" else requested[2]
        checked = replay.lean(metadata_seed + b"\n" + response,
                              "--chain", requested[0], str(argument))
        assert checked.returncode == 1 and b"rejected" in checked.stderr
        rejects_handoff(label, metadata_seed, *requested,
                        consumer=lambda prior, *_, actual=actual: replay.consume(prior, *actual))

    def rejects_bytes(name, payload):
        nonlocal rejected
        result = replay.lean(payload)
        assert result.returncode == 1 and b"rejected" in result.stderr, (name, result)
        result = replay.consume(payload, "shift", 0, 0)
        assert result.returncode == 1 and not result.stdout, (name, result)
        (output / f"reject-{name}.artifact").write_bytes(payload)
        rejected += 1

    good = seeds["mixed"]
    for name, payload in (
        ("empty", b""), ("truncated", good[:-1]), ("trailing", good + b";"),
        ("whitespace", good + b"\n"), ("invalid-byte", b"\xff" + good),
        ("noncanonical-one", b"10;" + good.split(b";", 1)[1]),
        ("noncanonical-zero", good.replace(b";;", b";0;", 1)),
        ("number-limit", b"1" * 65 + b";" + good.split(b";", 1)[1]),
        ("file-limit", good + b";" * (8 * 1024 * 1024)),
    ):
        rejects_bytes(name, payload)
    # One-node certificate in the same protocol, with targeted malformed fields.
    # These are rejection-only helpers, not accepted-artifact generation.
    def single(node, **kw):
        return canonical_tokens([kw.get("schema", 1), kw.get("input", 0), kw.get("output", 0),
                                 kw.get("operation", 0), kw.get("payload", 0), 1,
                                 *node, 1, *node])
    for name, payload in (
        ("schema", single([3], schema=2)), ("operation-tag", single([3], operation=2)),
        ("input-root", single([3], input=1)), ("output-root", single([3], output=1)),
        ("replacement-root", single([3], operation=1, payload=1)),
        ("unsupported-constructor", single([20])), ("forward-child", single([5, 1])),
        ("self-child", single([5, 0])), ("var-range", single([0, 2**32])),
        ("natural-range", single([1, 2**64])), ("integer-range", single([2, 0, 2**63])),
        ("negative-zero", single([2, 1, 0])), ("integer-sign", single([2, 2, 1])),
        ("binder-flag", single([8, 2, 0, 0])), ("elements-limit", single([11, 4097])),
        ("nodes-limit", canonical_tokens([1, 0, 0, 0, 0, 4097])),
        ("universe-limit", single([19, 33])),
        ("universe-u32-overflow", single([19, 2**32])),
    ):
        rejects_bytes(name, payload)
    for name, payload in (
        ("selected-prop", single([18])),
        ("selected-universe", single([19, 32])),
        ("reachable-prop", canonical_tokens([1, 1, 1, 0, 0, 2, 18, 5, 0, 2, 18, 5, 0])),
        ("reachable-universe", canonical_tokens([1, 1, 1, 0, 0, 2, 19, 0, 5, 0,
                                                2, 19, 0, 5, 0])),
        ("sort-replacement", canonical_tokens([1, 0, 0, 1, 1, 2, 3, 18, 2, 3, 18])),
    ):
        checked = replay.lean(payload)
        assert checked.returncode == 1 and b"rejected" in checked.stderr, (name, checked)
        # Parsing/re-exporting an exact sort is allowed. This cannot turn it into
        # an accepted Raw root: the runner checks Lean before any replay handoff.
        if name != "sort-replacement":
            assert replay.lean(require(replay.consume(payload, "shift", 0, 0))).returncode == 1
        rejected += 1
    # A bad unreachable sort level must be rejected by both graph checking and
    # the importer, even though the selected u64 node is otherwise supported.
    rejects_bytes("unreachable-universe-limit",
                  canonical_tokens([1, 0, 0, 0, 0, 2, 3, 19, 33, 2, 3, 19, 33]))
    for requested in (("shift", -1, 0), ("shift", 1001, 0), ("shift", 0, 1),
                      ("substitute", 1, 0), ("substitute", 0, 9999), ("rewrite", 0, 0)):
        result = replay.consume(good, *requested)
        assert result.returncode == 1 and not result.stdout
        rejected += 1
    # The only observed regression artifact here is an actual u32-overflow
    # result. The next consumer is never called because validation fails first.
    overflow = json.loads(require(command([str(snapshot), "shift", "overflow", "0"])))
    prior = replay.seed(overflow)
    invalid = require(replay.consume(prior, "shift", 1, 0))
    assert replay.lean(invalid).returncode == 1
    called = False

    def forbidden(*_):
        nonlocal called
        called = True
        raise AssertionError("invalid artifact reached next consumer")

    rejected_prior = replay.lean(invalid)
    assert rejected_prior.returncode == 1 and b"rejected" in rejected_prior.stderr
    try:
        replay.checked(invalid, "shift", 0, consumer=forbidden)
    except AssertionError:
        assert not called
        rejected += 1
    else:
        raise AssertionError("invalid prior artifact was accepted")
    print(f"canonical replay: {replay.validated} actual graph/root handoffs accepted; "
          f"{rejected} malformed, substituted, mismatched, or invalid handoffs rejected")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", default=os.environ.get("JIHOO_COMPILER", "jihoo"))
    parser.add_argument("--checker", default="lake env lean --run CheckArtifact.lean")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    compiler, checker = shlex.split(args.compiler), shlex.split(args.checker)
    if "/" in compiler[0]:
        compiler[0] = str((ROOT / compiler[0]).resolve())
    if args.output_dir:
        test(compiler, checker, args.output_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="jihoo-canonical-replay-") as path:
            test(compiler, checker, Path(path))


if __name__ == "__main__":
    main()
