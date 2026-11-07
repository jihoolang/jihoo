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
