# Checked typing artifacts

The typing-certificate checker independently checks a closed term and its type in
an exported constructor graph. It uses the beta-aware target judgment described
in the [Lean proof boundary](lean-proofs.md#beta-aware-target-conversion-and-contextual-preservation).
It does not assume that the compiler's acceptance implies a typing derivation.
This is certification of selected artifacts, not a proof of the executable
kernel's behavior on every program.

## What acceptance establishes

A certificate contains the complete graph, selected term and type roots, selected
final typing and formation steps, and a finite list of derivation steps. Each step
contains only numbers and graph references: a rule tag, context annotation roots,
subject/type roots, and references to earlier steps. There are no serialized Lean
proofs or producer-supplied assertions that the checker simply trusts.

The checker reconstructs each claim and its premises independently. It checks
exact equality of premise claims, not merely equal rule numbers or compatible
shapes. Forward references, cycles, wrong contexts, wrong arities, unsupported
rules and missing premises fail. The final two steps must establish both:

- `Raw.Beta.HasType` for the selected term at the selected type in the empty context.
- `Raw.Beta.IsType` for that selected type in the empty context.

Every step endpoint and context annotation decodes from the same complete graph.
Open substeps use finite telescopes: annotations are stored in their introduction
scope, newest first, and `Context.extend` performs weakening into the current
scope. An arbitrary intermediate context is not silently asserted to be well
formed; the final claim is closed, and binder rules require their own formation
premises. This release does not certify arbitrary externally supplied open
contexts.

`Typing.validate_sound` derives these judgments from executable validation alone.
`validate_exact_roots` additionally gives the representation relation for the
actual graph roots. `Typing.Wire.validateBytes_sound` connects the result to the
complete canonical byte artifact. The proof-producing checker constructs proofs
internally; its external input datatype contains no proof fields. Running its
compiled implementation still trusts the Lean toolchain and runtime.

## Explicit conversion evidence

The step language covers the target formation and typing rules, plus explicit
conversion derivations: reflexivity, symmetry, transitivity, beta, bounded closed
numeral addition and constructor congruence. A beta step recomputes
capture-avoiding substitution and checks its exact result. Application likewise
checks its substituted dependent result type. The checker does not attempt to
decide unrestricted beta equivalence by searching for a normal form.

This is the existing model, not a broader version of `Core.equal`. In particular,
the certificate producer must fail explicitly on unsupported features even when
the actual compiler accepts them. Examples include erased U64 binders, `zeroLe`
typing, `decide` with nonliteral endpoints, additional arithmetic identities,
proof irrelevance, globals and inductive families. The model's erasure flag must
equal its annotation's proposition classification. No universe typing rule was
added.

## Exact graph and byte association

Actual inference creates administrative `Prop` and `Universe` nodes, including
nodes not reachable from the selected term or type. The graph transport now
preserves these nodes and their original IDs. They have no child references;
universe levels are bounded below 33 because inference can produce level 32.
They are deliberately **not interpretable as Raw terms**. Selecting such a root,
or reaching one while decoding a selected term/type/context, still fails.

Existing graph tags 0–17 retain their encoding. Tags 18 and 19 carry the inert
sort nodes; old decoders reject those tags rather than misinterpreting them.
Transformation artifacts retain version 1. Typing artifacts use version 2 and
exported graph/root snapshots use version 3.

The snapshot-bound path retains the actual export bytes and compares the typed
artifact's complete graph and both roots against that independently supplied
snapshot. An unrelated but internally valid certificate is not enough. Both byte
formats have canonical codec guarantees; no field is silently repaired or
normalized. The producer cannot replace a graph or root merely because the new
one also has a valid derivation.

The test-only exporter calls the current `Core.check`, then ghost-mode
`Core.infer` or `Core.require`, and freezes every post-call node in order. The
untrusted producer builds explicit derivation data from that snapshot without
filtering nodes, renumbering IDs, or adding a separate graph of proof terms. It
may fail to find a certificate; producer completeness is not required for
acceptance soundness.

## Resource limits and checks

The CLI bounds input bytes, numeric token lengths, graph and proof-step counts,
context lengths and premise-vector lengths before invoking the recursive codec.
The pure checker also checks counts and graph validity, and budgets the aggregate
expanded size of every referenced root before unfolding terms. Repeated references
count repeatedly. Each premise occurrence also charges the expanded subject,
target and complete context of the referenced claim, including repeated premise
IDs. This prevents a wide rule from repeatedly comparing a large context while
paying for it only once. Potentially expanding beta/application substitutions have
additional structural size/depth guards before substitution.

These are conservative defensive limits, not a theorem bounding operating-system
resource usage. Exhausting a bound is a rejection, not evidence that the input is
ill typed. The producer is an untrusted bounded search procedure, not the theorem.

The integration suite invokes the actual core exporter, feeds its retained bytes
to the canonical validator, and exercises malformed derivations, exact-root and
whole-graph substitutions, wrong binder contexts, bad conversions, unsupported
features and resource limits. Run the grouped checks with the pinned toolchain:

```sh
nix build .#checks.x86_64-linux.lean-proofs -L
nix build .#checks.x86_64-linux.graph-certificates -L
```

## Remaining boundary

Artifact typing no longer requires trusting the certificate producer's proposed
derivation. The exporter still connects source text and an actual compiler
invocation to the snapshot; IO, compiler/toolchain identity and later consumers
remain outside the theorem. Nothing here proves that lowering consumes the same
graph or that every accepted core program can be certified.

The beta-aware target has contextual beta preservation, but this work does not
prove its closed semantic consistency, progress or normalization, all kernel
reductions, runtime ownership/erasure, lowering, or machine-code safety. Existing
[transformation certificates](graph-certificates.md) still have their stated
structural and conditional typing boundaries. A closed typing certificate is not
an automatic proof of every open body/replacement premise in that interface.

## Typed contextual beta replay

`TypedBeta.validate_sound` connects a checked closed input to **one** requested
beta contraction. A path is a list of zero-based constructor-child indices;
`[]` selects the root. Flags are not children. Pi/lambda children are annotation
then body; application children are function then argument; array elements use
their element index. Index and subtraction include their evidence child. Every
context constructor of `Raw.Beta.Step` is covered. An absent redex, invalid path,
reflexive conversion, or multiple contractions is rejected. The checker never
uses conversion alone as evidence of a requested step.

The version-4 replay record contains complete before/after version-3 snapshots
and the path. Validation also receives independently retained before/after
snapshots, the original version-2 typing artifact, and the independently requested
path. Literal equality binds both complete graphs, all roots, and that path.
The output's type root ID must equal the input's, and its decoded type must be
exactly the original decoded type. A convertible replacement type is insufficient.
The output term is checked against capture-avoiding contraction at the requested
path. Its typing is then **derived** from `Raw.Beta.HasType.preservation`; no
output typing derivation or open-context substitution premise is supplied.
`TypedBeta.Wire.validateBytes_sound` lifts this guarantee to canonical bytes.

The interface accepts a single step, not a chain. The shared bounded scanner caps
the entire four-artifact input at 8 MiB, each graph at 4096 nodes, numeric tokens
at 64 bits, and paths at 128 entries. Graph measurement counts every repeated
edge before unfolding. A fixed number of decoded term/type endpoints is used;
the existing aggregate typing-premise budget remains in force. At the redex,
`substitutionSafe` checks size and depth before substitution. These are defensive
limits, not an operating-system complexity theorem.

`tests/core_typed_beta_replay.jh` reconstructs the retained input graph without
renumbering, verifies its exact re-export, calls actual `Core.substitute` at the
selected location, rebuilds the enclosing path, and exports every resulting node.
The test orchestrator validates input typing before invoking this driver and
validates replay before calling a downstream consumer. Retained bytes, rather
than reread paths, are passed at both handoffs. The Python producer, importer,
exporter, compilation and IO association are still outside the theorem. This is
not a theorem about `Core.normal`, its reduction strategy, lowering, runtime
ownership, erasure, or machine code. The beta-aware model's closed semantic
consistency and all-program checker refinement remain open.

The grouped `lean-proofs` and `graph-certificates` Nix checks now include this
interface, executable constructor coverage, actual-Core positive examples,
canonical/association mutations, resource rejections and both handoff gates.

## Closed literal evidence observations

A further optional observer checks a requested literal equality or strict bound
against a typed snapshot. `Typing.Evidence.validateBytes_sound` binds the complete
canonical snapshot and typing artifact, checks the exact requested type root's
decoded term, and establishes `Realized`: closed typing, type formation,
weak-head normality, and truth of the requested mathematical relation. In
particular, accepted `Eq m n` evidence implies `m = n`, and accepted `Lt m n`
evidence implies `m < n`. The checker does **not** decide that arithmetic relation
as its acceptance test. Truth follows from the canonical-evidence theorem.

The observer accepts only literal endpoint types and closed evidence with no
beta redex on its function spine. It is deliberately not a normalizer. Lambda
bodies and constructor indices need not be normal: `refl ((lambda x: U64. x) 7)`
can be observed at the literal type `Eq 7 7` through a valid conversion proof.
Conversely, `(lambda x: U64. refl x) 7` is well typed but is rejected until its
head beta reduction is performed. A nonliteral requested type is also rejected,
even when its indices are convertible to literals. This is a specified
observation subset, not a restriction silently added to `Raw.Beta.HasType`.

The new canonical-form theorem is derived from the existing typing rules,
including conversion anywhere in a derivation. Church–Rosser supplies separation
of formed type heads, injectivity of equality/bound/array indices, and rigidity
of distinct numerals. A closed head-normal function must be a lambda; therefore
a closed typed head-normal application cannot be stuck. Closed equality evidence
is reflexivity and closed strict-bound evidence is literal `decide`, up to
conversion of their types. These facts imply the observed literal truth.

`Typing.Evidence.replay_realized` composes this result with typed beta replay:
if the validated output passes the observer, its semantic conclusion follows
without an independently supplied output typing certificate. The general
`HasType.reduces_literal_eq/lt` lemmas also accept an explicit finite beta-reduction
witness reaching a head-normal output. They do not assume that such a witness
exists for every well-typed term.

The shared IO byte, graph, proof and token limits remain in force; CLI endpoints
are bounded U64 numerals. Run `lake env lean --run CheckEvidence.lean eq 7 7`
(or `lt 1 2`) with `snapshot LF typing-artifact` on stdin. The grouped Nix checks
exercise actual-Core exports, higher-order index expressions, unnormalized
indices, independently typed unsupported observations, wrong requests, exact
snapshot substitutions, malformed bytes, and false claims.

**Remaining obligation:** these are conditional canonical-evidence results,
not full semantic realization of arbitrary higher-order terms or an unconditional
consistency theorem for `Raw.Beta`. Universal weak-head normalization, a full
relational semantics, operational adequacy, exporter fidelity, checker refinement,
and runtime/compiler soundness remain unproved.

## Finite head-normalization witnesses

The version-5 normalization witness is a finite list of version-4 beta replay
records. The input snapshot, final output snapshot and original input typing
artifact are supplied independently. Every record's entire `before` snapshot
must equal the preceding retained state, including unreachable nodes and both
root IDs. The last record's `after` snapshot must equal the independently retained
output. An empty witness requires literal input/output snapshot equality.

Each step recomputes a deterministic function-spine path: contract the current
application if its function is a lambda; otherwise search only its function
child. Arguments, lambda bodies and annotations are not searched. The validator
checks the exact capture-avoiding contraction at that path, rather than accepting
convertibility or a different valid beta step. The original type root ID and its
exact decoded type are preserved at every step. `Trace.reduction` derives a
finite `Raw.Beta.Steps` witness, and `validate_original_type` derives output typing
at the original decoded input type. No output typing certificate is needed.

A complete witness must end at `Raw.Beta.headNormal`. Prefix validation is a
separate interface that proves typed continuity but makes no normality claim.
The untrusted producer validates each prefix before passing its retained output
to the next actual `Core.substitute` invocation. It validates the final witness
before publication. Literal mode additionally applies the previous observer;
`HeadNormalization.Wire.validateLiteralBytes_truth` derives the requested equality
or strict inequality from successful normalization and original typing. The
checker never directly tests the requested arithmetic relation.

### Bounds and failures

The verifier caps a chain at 64 steps, each path at 128 entries, the complete
four-artifact input at 8 MiB and numeric tokens at 64 bits. Each graph retains the
4096-node, 200000-expanded-occurrence and depth-128 limits. Aggregate serialized
snapshot occurrences are capped at 32768 nodes. An additional 2000000-unit budget
charges four times the expanded term and type root sizes for **each snapshot
occurrence**, including duplicate graphs and repeated roots. Measurement happens
before unfolding. The original typing derivation has its own premise-work
budget. Selected substitutions have the existing size-product/depth guards.

The producer accepts fuel from 0 through 64 and measures the selected graph
substitution before invoking Core. It emits no partial result on fuel exhaustion,
budget exhaustion, malformed input, failed subprocesses, mismatched prefixes or
failed final validation. Inputs are read once with bounds; only retained bytes
cross handoffs. Prefix revalidation has potentially quadratic orchestration cost
within the fixed step cap. These are conservative defensive bounds, not an OS
resource theorem or evidence that rejected programs are ill typed.

The verifier is `lake env lean --run CheckNormalization.lean` with
`input-snapshot LF output-snapshot LF input-typing LF chain` on stdin. Optional
`eq LEFT RIGHT` or `lt LEFT RIGHT` requests literal truth; `--prefix` checks only
a typed prefix. The reusable test producer is:

```sh
python3 tests/core_head_normalization.py \
  --generate input.snapshot input.typing --driver ./core-typed-beta-replay \
  --fuel 64 --claim eq 7 7 > checked-normalization.bundle
```

The driver is built from `tests/core_typed_beta_replay.jh` against the current
compiler. Omitting `--generate` runs its integration tests. The grouped Nix checks
exercise actual zero-, one- and multi-step witnesses, higher-order inputs,
non-head valid beta steps, skipped/reordered/duplicated records, exact graph/root
substitutions, aggregate repeated-reference budgets, fuel failures, intermediate
handoff rejection and read-once final publication.

**Remaining boundary:** success certifies one finite supplied trace and its
head-normal endpoint. Fuel-bounded search is not universal normalization or a
proof that every accepted core program has a witness. Constructor indices and
lambda bodies may remain unreduced, and a nonliteral type is not normalized by
this interface. Importer/exporter and IO fidelity, `Core.normal` strategy,
higher-order denotational realization, unconditional consistency, runtime
erasure/ownership and lowering remain outside the theorem.


## Finite type-index normalization after head normalization

`TypeIndexNormalization.lean` closes an observation gap left by the literal-only
endpoint. For example, a certified term at `Eq ((lambda x. x) 7) 7` cannot pass
an observation requesting the exact type `Eq 7 7`, even if its evidence term is
already head normal. A second finite, checked trace now reduces the original
proposition's indices and transports that same evidence term to the resulting
type. The requested arithmetic truth is still derived from typing and canonical
forms, not supplied as a premise or tested directly by the observation checker.

There are two distinct trace roles:

1. The existing head trace reduces the term while preserving its original type
   root and decoded type, and proves a head-normal middle snapshot.
2. The type-index trace reduces the type while preserving the exact term root
   ID and decoded evidence term. Each transition proves `Beta.Step A B`, derives
   formation of B by `IsType.preservation`, and transports term typing using
   the step's proved conversion. It does not request an output typing certificate.

The deterministic type policy handles only `Eq` and `Lt`: reduce the left
index's function spine first, then the right index's function spine. It does
not normalize constructor children, lambda bodies, arithmetic, general Pi
types or arbitrary convertible types. Consequently a true `Eq (3 + 4) 7`
observation is intentionally rejected by this beta-only policy. There is no
claim that every well-typed index reaches a literal.

`validate_lineage` exposes both reductions explicitly: the original term
reduces at its original decoded type, the original type reduces to the requested
literal proposition, and the retained resulting evidence has both the original
and final types. `validate_truth` derives the requested equality or bound;
`false_claim_rejected` excludes false literal claims. The full graph and both
roots are compared at the shared phase boundary and at every record boundary,
including unreachable nodes. A term-root record cannot be substituted into the
type-root phase, and a different output root is not interchangeable with an
independently supplied output snapshot merely because it decodes equivalently.

The CLI consumes six canonical artifacts separated by LF:

```
input snapshot LF middle snapshot LF output snapshot LF input typing LF head chain LF type chain
```

Both chains reuse schema-5 lists of schema-4 before/after/path records. Their
fixed positions in this envelope determine the operation's root; the record
syntax alone does not authorize either role. `TypeIndexNormalization.Wire`
proves exact canonical byte identities for all six artifacts on acceptance.
`CheckTypeNormalization.lean eq M N` or `lt M N` requires the final literal
observation. `--prefix` checks a head-normal first phase and a possibly unfinished
type trace; it is never sufficient for publishing a completed literal result.

The 8 MiB total CLI input bound, 4096 nodes per graph, 128 path/depth bound,
32768 aggregate serialized nodes and 2000000 charged expanded work remain.
The 64-step cap and aggregate node/work caps apply to the **combined** head and
type chains, counting repeated graph/root occurrences. Existing typing search
has its separate bounds. Pure validation measures graph expansions before
unfolding, and the producer guards each selected substitution before invoking
Core. These are finite resource guards, not a proved time-complexity bound.

The untrusted producer is executable as:

```sh
python3 tests/core_type_index_normalization.py \
  --generate retained.snapshot retained.typing \
  --driver /path/to/core-typed-beta-replay --claim eq 7 7 --fuel 64
```

The replay driver now takes explicit `--type` to call actual `Core.substitute`
at the type root. Its existing term-root mode is unchanged. The producer reads
each supplied artifact once, validates the original input before reduction,
checks the combined prefix before the first and each subsequent type operation,
and emits a bundle only after the complete requested observation passes.
Invalid intermediate graphs and fuel/resource failure prevent further use or
publication. Tests exercise real-Core equality and bound indices, both phases,
higher-order arguments, retained-file replacement, role swaps, changed evidence,
root/graph mutations, valid but out-of-policy steps, incomplete traces, shared
limits and producer failure without partial stdout.

This is a successful finite-trace theorem for the declarative fragment. It does
not prove general higher-order realization, weak/strong normalization, all-term
consistency, source/exporter fidelity, actual `Core.normal` equivalence, runtime
behavior or full compiler soundness. The existing untrusted typing-certificate
producer can also reject valid core terms when it cannot find the required
conversion intermediates; no completeness theorem is introduced here.


## Closed consistency without a supplied normalization trace

The proof-only `TypingClosedConsistency.lean` layer uses the new closed head
normalization theorem for `Raw.Beta.HasType` to strengthen the consequence of the
**existing** exact-snapshot typing validator. Accepted input has some finite
head-normal Raw result, and an exact independently selected literal Eq/Lt type
has true endpoints without requiring a separate reduction certificate or an
initially head-normal evidence term. The checker still validates typing rather
than directly deciding the requested arithmetic relation.

This introduces no new executable observer, wire format or acceptance rule.
Existing head/type normalization tools still validate each actual retained
snapshot, reject incomplete traces, and enforce their unchanged resource caps.
The existence theorem does not produce a graph or imply that a bounded producer
succeeds. It concerns closed declarative head beta only, not full contextual
normalization, symbolic arithmetic, `Core.normal`, runtime execution, exporter
fidelity or full compiler soundness. See the closed-head-normalization section
of [lean-proofs.md](lean-proofs.md) for the precise theorem chain and limits.


## Actual ghost Core.normal result validation

`CheckCoreNormal.lean DEPTH FUEL` checks four LF-separated canonical artifacts:
input snapshot, output snapshot, original input typing certificate, and a
schema-6 operation record. The record encodes `6; depth; fuel; before; after`
using the existing canonical number/snapshot encoding. Version 6 fixes ghost
Core.normal as the operation; it is not a beta-path or type-root replay record.
`--input DEPTH FUEL` consumes just input snapshot LF typing and admits only an
input for which bounded, independently proved beta/add normalization succeeds.
The producer always uses this gate before invoking the actual Core method.

```sh
python3 tests/core_checked_normalization.py \
  --generate retained.snapshot retained.typing \
  --driver /path/to/core-typed-beta-replay --depth 128 --fuel 64
```

The driver receives `--normal DEPTH FUEL`, explicitly sets ghost mode and invokes
`Core.normal` once. The final checker binds the exact retained output and request
record, verifies the unchanged whole input graph prefix, and derives output
typing at the original type from a directed contextual beta/literal-add proof.
The proof-producing normalizer has total-step, expanded-size, depth and selected
substitution-product limits. Failure or incomplete/unsupported normalization
never falls back to mere conversion or assumes output typing.

This conservative profile rejects symbolic UAdd, overflow, subtraction, ZeroLe,
indexing and array values. Some closed inputs are rejected because their lambda
bodies contain symbolic arithmetic before beta contraction. Core's broader
symbolic normalization is not modeled. This is checked per-run output within the
profile, not a formal proof of the Core implementation or its general termination.
See [lean-proofs.md](lean-proofs.md) for the exact semantic and resource boundaries.
