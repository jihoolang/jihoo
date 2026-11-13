# Node child consumption

Base: `3facf6fb2b2bba8f1e3c954c6c16a7aaf402bac4`.

`CommonCaseChildConsumption.lean` proves a narrow route through the ownership
seam without changing any typing rule. A literal-only Node branch is genuinely
untypable: `literal_inventory_zero` inverts all source typing constructors, and
`no_node_literal_body` rules out a literal BodyResult immediately after Node
entry. This remains true for two logical Nil children: capability count is not
allocation footprint, and target Nil is boxed.

The explicit replacement source body is `drop left; drop right; integer n`.
Node lexical order is right at slot index 0, left at index 1. The inventory is
left then right. Dropping left shifts right's capability index to zero while
preserving its lexical position. Both removals retire every consumed alias.
This is a different source term, not an implicit permission to add drops to the
original literal's evaluation or to discard its children.

Proved results:

- `typed`: the explicit body consumes exactly two data capabilities, with any
  outer context and any number of ghost binders, and no buffers.
- `total`: source execution and allocation accounting follow from initial
  agreement, empty buffer layout, valid heap, ownership and field representation.
- `child_released`: every tracked child allocation is freed exactly once and dead.
- `frame_survives`: disjoint ambient identities stay live and are never freed.
  The parent shell can inhabit this frame; ownership separation is required.
- `installed_children`: two calls to the existing installed recursive Tree Drop
  function produce actual ReferenceCalls.Steps in one program, both source
  Destroy derivations, and a CommonContext with empty images/buffers/sizes.
  Pending shells, source/target frames, environment and lexical slots are
  retained. The context's shell validity only asserts authority over the shell;
  its old child pointers may be stale after the drops.

The installed theorem assumes a valid initial CommonContext with exactly two
images and no buffers; a signed literal bound; the exact TreeDropCall body
installed at dropId; first and second call-site type/bounds/extension checks;
unit destinations fresh for surviving lexical bindings; and stack limits of
caller depth + 1 + child image depth. The second site's structural checks are
quantified over the first call's output heap. They do not assume success,
resource consumption, or the theorem conclusion. Both recursive calls are
proved by the existing typed_drop_prefix theorem. The theorem is polymorphic
in child images, including nonempty recursive trees.

Checks in `CommonCaseChildConsumptionChecks.lean` cover ghost/outer aliases,
literal rejection, actual ten-tick execution of two installed boxed-Nil drop
calls, and unchanged parent object. Axiom audits report only propext,
Classical.choice and Quot.sound (subsets thereof for simpler results); there
are no added axioms or proof holes.

Follow-up: `CommonCaseChildTransfer.lean` now packages exact call ticks and
constructs the explicit drop/drop/literal `BodyResult` for arbitrary child
images. Its checks construct a closed entry/body/installed-finish pipeline in
one larger installed program. See `CASE_CHILD_TRANSFER.md` for premises,
24-tick closed integration, the recursive-child execution check, and validation.

Remaining work includes a parameterized Case linker, the enclosing source Case
graph, and extension of the frozen `Supported` subset to explicit drops. No
compiler lowering theorem, full Case correctness, native semantics or
source/target trace equality is claimed. Source frees omit logical Nil; target
traces free the boxes too.

Validation used Lean 4.34.1 with `-DwarningAsError=true`, compiling the new module
and checks and rerunning CommonLiteralFinishChecks. Unchanged dependency oleans
were reused from the integration worktree; this was not a clean whole-library
build. No CI or existing proof files were modified.
