# Recursive child roots in lexical environments

`RecursiveLexicalFields` extends the abstract cell-store model with a semantic
lexical relation. `enter` takes a runtime state, an environment, a lexical
index, and an erased-slot count. It reads the selected Data root and its actual
cell, then binds the stored right and left roots. It receives no tree witness
or flattened ownership list. In the fixture the right value is root `2`,
while its ownership footprint is `[2,3]`.

`enter_total` proves that an agreeing environment and owned, represented
parent tree suffice for successful entry. The resulting environment agrees
with the two child capabilities. Every old alias of the parent capability
becomes `dead`, while all remaining capability indices shift by one. Runtime
stale pointers stay in dead slots; they do not retain lexical authority.
The heap is unchanged. Ownership of the parent shell is retained separately
from the active child inventory as `Owns heap (parent :: footprint children)`.
`finish_safe` consumes that pending shell and preserves child representation
and ownership. It requires the pending ownership and field representation at
finish time; preservation by an arbitrary case body is not proved.

The fixed declaration layout is `[erased slots..., left, right]`, hence the
newest-first lexical environment is `[right, left, ghosts..., outer...]`.
The selected parent capability must head the semantic inventory, although
its lexical aliases may appear at any index. Empty children use `none` roots.
Erased slots carry only `.ghost`: no past-value truth, equality transport,
dependent motive, or constructor-telescope interpretation is established.

## Connection to existing Core typing

`Jihoo.RecursiveLexicalFields.Agrees.toSized` (in
`RecursiveLexicalBufferBridge.lean`) recovers the established
`SizedBufferContext.Agrees` for a Buffer-only inventory and embedded original
context/environment. `buffer_total` then uses the original
`SizedCoreTyping.Typing.total_accounted` to derive execution, safe steps,
validity, result ownership and exact resource accounting. Original `Layout`
and typing premises remain required; erased bounds are retained from that
original context, not inferred from a ghost. Data and Buffer values are
distinct, and this bridge never turns recursive fields into Buffers.

The regression suite instantiates this connection with the existing sized
allocation/lend/read/free graph for every closing length/index, and checks a
nonempty Buffer environment. Other examples check actual root order, two
separated parent aliases, mixed Buffer/Data tail slots, multiple erased slots,
delayed parent release, retained children, and malformed runtime entry.

## Remaining boundary

This is a closing-instance semantic interface, not a source `Case` typing
rule or a native compiler proof. `ScopedLend.Graph.Node` still lacks recursive
constructors and eliminators. A common typing theorem still needs source
constructor signatures, tags and branch coverage, typing-directed inventory
transitions, body preservation, and general recursive-family interpretation.
Dependent Case needs motive/substitution and erased evidence preservation;
none follows merely from binding ghost slots.

Raw `enter` is a read-only store operation and can be repeated with an old
environment. The semantic context transition retires its authority; enforcing
that transition in source programs remains the future Case rule's job.
Likewise, the pending shell corresponds only to a restricted delayed-free
model. Production lowering can reuse pending nodes and flushes them at block
boundaries; no arbitrary lowering trace, native byte layout, reuse behavior,
or equivalence with the earlier eager `take` operation is claimed.

Run `bash proofs/check-recursive-fields.sh` with pinned Lean and Python, or
`nix build .#checks.x86_64-linux.recursive-field-proofs`. This uses the existing
standalone CI check and leaves shared proof aggregators and compiler sources
unchanged. These results do not close the 0.6 common-Core soundness gate.
