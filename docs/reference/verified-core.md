# Verified Core subset check

`python3 scripts/verified_core.py` is an explicit, fail-closed dual-check
operation for one closed textual Core proof declaration. It runs the native
Core checker **and** independently admits the original term and declared type
with Lean. Ordinary `jihoo check` and compilation are unchanged and do not
invoke Lean. This operation does not compile or execute the submitted program.

## Build and run

From the repository root, in `nix develop` with this checkout's compiler built:

```sh
out/jihoo build -O0 -I compiler compiler/verified_core_snapshot.jh -o out/verified-core-snapshot
(cd proofs && lake build --wfail)
python3 scripts/verified_core.py --exporter out/verified-core-snapshot examples/verified-core/identity.core
```

Python 3, the repository-pinned Lean/Lake toolchain, and a **trusted exporter
built from the same checkout** are required. The exporter is not a verifier;
never interpret its exit status or output alone as successful proof checking.
`--exporter` selects a trusted local executable, not a certificate producer
provided by an untrusted input. Run this command only from a trusted checkout
and toolchain (including its Lake configuration and PATH).

Input `-` reads one source value from stdin. The command emits exactly one JSON
object on stdout only after all checks succeed, with `status: verified-subset`,
`scope: closed-mixed-proof-v1`, and SHA-256 digests of the retained source and
snapshot bytes. On any failure it exits nonzero, writes diagnostics to stderr,
and emits no success JSON. There is no output artifact, execution callback or
fallback to ordinary compiler acceptance. Consumers must check exit status and
parse the complete JSON; an old log or a substring is not an acceptance result.

## What is accepted

The initial subset is intentionally narrow: a single closed declaration, no
families or globals, mixed natural-index lambdas/applications and erased proof
lambdas/applications, Eq/Lt, Refl, ZeroLe and representable Decide evidence.
Natural application arguments must satisfy the existing atomic restriction.
The declared type must parse and match independently inferred syntax exactly;
a merely convertible alternative is not substituted silently. Unsupported
constructors, annotations or conversion reject even if native Core accepts.

The `identity.core` example checks the dependent proposition that for any
natural index `n`, evidence of `Eq n n` can be returned unchanged. It is a useful
way to check small closed dependent proof combinators through two distinct
checks, not a general jihoo program-verification command.

## Result and limits

`Jihoo.VerifiedCore.execution_safety` composes exact snapshot admission with
strict evaluation: the decoded original term has its requested type, every
finite strict execution preserves that same type, and its endpoint is a value,
can take a step, or has an explicit overflow trap. `requested_truth` retains
truth of the separately parsed requested proposition. `erased_execution`
preserves source steps under annotation/computed-proof-payload removal, which
retains binder slots and is not complete native erasure.

These are theorems about independently admitted decoded terms. This is **not**
a proof that arbitrary `Core.check`, `infer` or `require` acceptance is sound,
nor a native/compiler/LLVM refinement, termination, ownership or heap theorem.
Native parsing and export, executable association, IO, Python orchestration and
the Lean runtime/toolchain remain trusted. The byte hashes identify the retained
inputs; they do not prove that a malicious exporter faithfully translated the
source. The verifier's exact-byte response prevents accidental substitution or
stale-response reuse between the two subprocess calls, not a malicious verifier.

## Bounds and failures

The adapter reads source bytes once (at most 1 MiB), sends that value directly
to the fixed-require exporter, retains one complete snapshot (at most 8 MiB),
and sends those same bytes to the verifier. It never rereads the source path.
Both subprocesses have a 180-second wall-clock deadline and bounded stdout and
stderr (64 KiB diagnostic limit). Overflow and timeout terminate the process
group. A nonzero exit rejects even if stdout looks valid. Missing tools,
malformed or trailing protocol output and a response for different bytes reject.
Lean additionally checks canonical graph shape, all nodes including unused nodes,
root identity, graph limits and the existing bounded mixed-admission limits.
These are explicit resource guards, not a proof of a fixed OS RSS bound.

## Regression checks

```sh
python3 tests/verified_core.py --compiler out/jihoo
python3 -O tests/verified_core.py --compiler out/jihoo
```

The suite covers actual accepted programs, native-accepted but unsupported
programs, requested-type mismatch, malformed graphs, exact protocol/byte
association, failed producers/verifiers, bounded simultaneous pipe handling,
missing tools, timeout and output floods. The existing mixed-admission graph
mutation suite continues to exercise its underlying semantic gate.
