# Graph artifact certificates

This check connects concrete exported core graphs to a Lean model of binder-aware
transformation. It is **artifact certification**, not a theorem about every
execution of `compiler/core.jh`, and not full compiler soundness.

## What is checked

A test driver imports the current core implementation, constructs representative
term graphs, and calls its actual `shift` and `substitute` methods. The resulting
certificate identifies the operation, parameters, input and output roots, and
before/after graph snapshots. It is checked independently of whether the compiler
reported the transformation as successful.

The validator decodes a bounded, supported graph fragment into the existing
unified `Raw` syntax. It rejects malformed references and unsupported constructors
instead of replacing them with a default term. A successful certificate establishes
the claimed relation between the decoded input and output. The reference operation
uses capture-avoiding renaming or substitution, including beneath lambda and Pi
binders and within their annotations.

The before/after distinction matters: a transformation cannot establish its result
by changing the input graph and then checking against that changed input. The
certificate checks retain the original graph and verify append-only preservation.

## Trust boundary

The proof establishes properties of the data passed to the formal validator. The
exporter and test runner remain trusted to identify those data with the actual
mutable `Core` graph and the operation that ran. A hash can bind exact bytes, but
cannot prove that an unverified exporter copied the intended graph correctly.
The JSON parser and IO path are not themselves proved equivalent to an external
serialization specification.

The certificates do not become the sole artifact consumed by lowering. Consequently
validation does not establish that a later compilation stage consumes exactly the
certified graph. Closing that association requires an integration design, not just
a stronger claim about the existing tests.

The Lean kernel and standard logical foundation remain trusted, as does the
installed toolchain used to execute the check. No assumption that the compiler's
output is correct is needed by the pure validation theorem.

## What this does not establish

- Success or correctness of every call to `Core.shift` or `Core.substitute`.
- Correctness of `Core.check`, its normalization-based conversion, graph caches,
  declaration ordering or resource-budget handling.
- Typing, preservation, consistency or runtime safety of the certified graph.
- Correctness of runtime erasure, ownership checks, lowering or machine code.

Even a future certificate establishing the restricted `Raw.HasType` judgment
would initially certify typing only: that target judgment does not yet have its
own general preservation or semantic soundness theorem. The earlier source
consistency theorem cannot be transported backward through a one-way source-to-target
typing translation.

A universal theorem about the implementation requires a formal execution connection,
such as a verified restricted embedding of the relevant Jihoo functions. A second
handwritten Lean implementation with differential tests would still leave that
connection unproved.

## Supported operations and limits

The first certificate format supports nonnegative shifts at cutoff zero and
substitution of the outermost binder. Negative shifts, nonzero cutoffs and the
core's separate `rewrite` operation are outside this format. The graph vocabulary
is the selected `Raw` constructor set, not every core constructor. Graphs need
not be typable: this check establishes a structural transformation property.

The validator limits each graph to 4,096 nodes and each child vector to 4,096
entries. It checks backward references throughout each graph, including nodes
unreachable from the selected root. Variable indices must fit u32, natural
literals u64, and integer literals i64. A depth limit of 128 and a preflight
unfolding-size limit of 200,000 tree occurrences prevent a small shared DAG from
being expanded without a bound. These stricter limits may reject operations that
the compiler could otherwise perform; completeness is not claimed.

Before computing expected substitution, a conservative guard checks the product
of the measured input and replacement sizes, and the sum of their depths. This
prevents individually bounded trees from triggering unchecked duplication in the
reference substitution. The size/work preflight is defensive executable code,
not a proved time or memory complexity theorem.

The byte adapter caps files at 8 MiB and accepts a small JSON vocabulary: exact
fields and constructor arities, integral numeric payloads, Boolean erasure flags,
and fixed schema/operation metadata. These parsing and resource checks are tested,
but the formal statement starts with the parsed certificate datatype.

## Reproducing the integration check

With the repository's pinned Nix inputs:

```sh
nix build .#checks.x86_64-linux.graph-certificates -L
# On an aarch64 host, use checks.aarch64-linux.graph-certificates.
```

The ordinary two-platform `nix flake check` includes this derivation. It builds a
test-only exporter against this checkout's `compiler/core.jh`, runs actual
transformations, and passes their stdout to the Lean certificate validator.
It does not compare only against a hand-maintained expected fixture.

With a built compiler, Lean 4.34.1 and Python 3 available:

```sh
(cd proofs && lake build --wfail)
python3 tests/core_transform_certificates.py --compiler out/jihoo
```

Use `--output-dir` to retain the snapshots and provenance manifest. The manifest
records source hashes and commands for inspection; those hashes are not a proof
of exporter honesty or execution fidelity.

## Formal guarantees

The audited declarations include `decode_sound`, `decode_graph_bounds` and
`decode_root_bound`. They connect the executable decoder to an independently
defined, depth-indexed graph representation and establish graph/reference/payload
bounds. `rawEqual_iff` proves that the structural comparison used by validation
is exact, including arrays of subterms.

`validate_sound` establishes the original graph prefix and the decoded input/output
relation. `validate_shift` and `validate_substitute` specialize that result to
`Raw.rename` and capture-avoiding `Raw.subst`. These are implications from a
computed acceptance result; the claimed output equality is not an input premise.

The integration suite also rejects an actual transform result obtained by shifting
a maximal u32 variable index. That cast wraps in the implementation, whereas
mathematical renaming does not. The input is an open, untyped graph, not an accepted
program: this test demonstrates a useful certificate rejection, not a flaw in
`Core.infer` soundness.

Four tiny kernel-checked examples establish successful shift, capture-avoiding
substitution beneath mixed Pi/lambda binders, and rejection of a malformed root
and changed input prefix. Separate executable assertions exercise the substitution
size-product/depth-sum guards with individually valid input graphs. The integration
suite accepts 15 actual exported transformations and rejects 59 malformed, tampered
or wrapping results, plus six unsupported or failed exporter invocations.

## Canonical artifact replay

The replay path narrows the association gap for successive transformations. Its
input is the complete previous validated certificate, not an independently
reconstructed JSON description or a hidden original compiler graph. The next input
graph is exactly that certificate's `after` graph, and its root is exactly `output`.
There is no separate root override.

The canonical format retains every constructor, payload, child index and operation
field. Natural numbers use little-endian ASCII binary digits terminated by a
semicolon; zero is the terminator alone. Thus large numeric literals need a number
of digits proportional to their bit width, not a unary expansion. Signed integers
and Boolean fields have fixed interpretations in the codec.

The runner reads the prior artifact once and retains its bytes. Lean validates
those bytes, and the test-only Jihoo driver receives the same retained bytes on
stdin. The driver constructs a fresh `Core` graph in index order and re-exports its
actual nodes to check canonical identity before invoking the requested operation.
The emitted next certificate is checked against the prior artifact for exact
before/after graph and root continuity, not just mathematical equality of selected
subtrees or matching hashes.

This is still not a theorem about executing Jihoo or about the honesty of the
importer/exporter. The smaller integration boundary includes the stdin/IO path,
the reconstruction/round-trip guard, and invocation of the operation on that same
reconstruction. The canonical codec theorem establishes artifact identity, while
the transformation theorem establishes the stated relation on decoded artifacts.
Neither alone proves that the implementation followed the integration protocol.
The ordinary lowering pipeline does not consume this certified replay chain.

### Codec and chain guarantees

`Canonical.decodeCertificate_encode` proves byte-level roundtrip for every
certificate. `Canonical.encodeCertificate_injective` proves that the canonical
encoding cannot identify two different certificates. `Canonical.decodeCertificate_exact`
proves that every accepted complete decoding re-encodes to exactly the supplied
bytes, rejecting trailing bytes and nonminimal numeral encodings. These results
concern actual `ByteArray` values, not only an abstract token stream.

`validateChain_sound` proves exact graph/root continuity and composition of the
selected transformations across a checked list. `validateRequested_sound` also
checks an operation supplied independently of the artifact's self-description.
`Canonical.validateReplay_sound` ties these properties to the exact previous and
next artifact bytes. An individually valid but unrelated certificate therefore
cannot satisfy the replay handoff merely because its selected term has the same
meaning.

The generic codec is total over the mathematical datatype. Before running its
recursive parser, the runtime CLI separately checks file/token limits and bounds
graph and child-vector counts. This defensive preflight limits work on malicious
inputs; it is not a theorem about OS resource consumption. Canonical-byte decoding
is proved, while the initial JSON-to-certificate adapter and external IO/execution
remain outside that proof.

### Replay checks

The same `graph-certificates` Nix check also builds the replay driver and runs
`tests/core_artifact_replay.py`. It exercises real chained transformations, a file
replacement after the single input read, and individually valid but unrelated
certificates. It checks selected-root/full-graph continuity and rejects requested
operation mismatches even when the different operations produce the same graph.
Nine tiny kernel examples cover accepted replay, multiple-step composition and
representative byte/metadata/root/graph rejections.

To run this part alone with the built compiler and pinned Lean toolchain:

```sh
(cd proofs && lake build --wfail)
python3 tests/core_artifact_replay.py --compiler out/jihoo
```

## Conditional typing of transformed artifacts

A structural certificate alone does not establish typing. A typed-substitution
bridge can additionally use a derivation for the exact decoded input body in a
context extended by its argument type, and a derivation for the exact decoded
replacement in the original context. It then derives typing of the certified
output at the correspondingly substituted result type. Output typing is the
conclusion, not another assumed certificate field.

Those input/replacement derivations are separate premises. Neither `CheckGraph`
nor `CheckArtifact` currently validates typing-derivation certificates or infers
those premises. The intentionally untyped transformation fixtures therefore
remain valid structural tests, without acquiring a typing or safety guarantee.
Head-beta retyping also does not imply unrestricted contextual beta preservation;
the [target-model limitation](lean-proofs.md#why-unrestricted-contextual-preservation-is-not-claimed)
explains why the unchanged conversion relation cannot support that claim.

The bridge theorems are `validate_shift_typed` and `validate_substitute_typed`.
Their premises name the certificate's exact operation and decoded input/replacement
roots. The result includes the decoded output at the certificate's actual output
root and its derived target typing. A shift also requires the matching context
renaming relation; substitution instantiates both the term and its result type.
