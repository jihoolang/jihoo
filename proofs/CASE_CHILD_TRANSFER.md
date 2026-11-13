# Exact child-drop body transfer

Base: `41415f06ddce0b1d40dd35a4b0eebc753d2d1c7b`.

`CommonCaseChildTransfer.lean` constructs an exact `BodyResult` for the changed
source body `drop left; drop right; integer n`. It does not make the original
literal-only Node body typable and does not discard child ownership.

## Generic results

- `walk_eq` equates the two existing bounded walkers by induction.
- `invoke_exact` derives a bounded walk for one installed recursive drop call:
  one call instruction, `TreeDropCall.ticks image` body instructions, and one
  return instruction. It also returns the heap `Frees` relation. It uses the
  installed drop body and call site, not `Steps` or a desired walk as a premise.
- `drop_exact` adds source destruction, the selected source lexical value, and
  the surviving `CommonContext`. It preserves pending shells and both frames.
- `body` constructs source typing, source `Eval`, exact target `Transfer`,
  scalar ownership, and a result-local relation. Its tick count is
  `(1 + ticks left + 1) + (1 + ticks right + 1) + 2`.
  `ticks Nil = 3`; `ticks (Node l r) = 13 + ticks l + ticks r`.
  Children may be arbitrary recursive images. Their source frees and target
  frees remain separate traces: logical source Nil has no allocation, while
  its target representation owns a box.

The generic body assumptions are explicit:

1. A valid initial boundary with exactly two data images, no buffers or sizes,
   and a Node-bound lexical context (arbitrary ghosts and outer context).
2. A signed literal, `n < 2^63`.
3. The actual recursive drop function installed at `dropId` in one program.
4. Both call-site type, local-space, continuation and extension checks; the
   second site's checks are uniform over the first call's output heap.
5. Unit destinations fresh for surviving lexical bindings after their drops,
   and a scalar destination fresh after both drops.
6. Each child's independent stack bound:
   `initial.stack.length + 1 + child.depth ≤ limit`.
7. `LiteralSite` checks for the installed assignment/goto block, no overriding
   extension, index zero, i64 destination type and space, and continuation
   bounds. These are uniform over source states and output heaps; they contain
   no execution or ownership-success premise.

`Boundary.Valid` supplies source validity, lexical agreement and target bindings,
resource representations, disjoint ownership, pending-shell authority and buffer
layout. In particular, pending-shell and ambient identities are separated from
both child footprints. Shell validity permits stale child pointers after drops;
it does not permit dereferencing them.

## Closed integration and regressions

`CommonCaseChildTransferChecks.lean` installs the copied Case entry blocks,
two drop call exits, literal block, shell free, and recursive drop function in
one explicit program. Its input context and all structural premises are proved.
The original `CaseInput.program` has one function and no call extensions, so
it cannot itself host these calls. The fixture reuses the entry ownership
transformation, and separately kernel-checks the 11 entry ticks in the actual
larger program. It does not assume equivalence of the two programs.

- `pipeline`: entry 11 + two boxed-Nil calls 10 + literal 2 + shell free 1 =
  exactly 24 ticks, with events `[free 1, free 2, free 3]`.
- `complete`: constructs the final valid boundary and scalar ownership, proves
  result 7 in local 1, retained scalar 77 in local 8, the same suspended caller,
  source frame `[4]`, target frame `[0]`, and an empty pending list.
- `exact_walk` and `one_tick_short`: concrete machine endpoints at 24 and 23
  ticks; at 23 ticks the parent shell has not yet been freed.
- `insufficient_stack` and `result_collision_rejected`: reject insufficient
  stack budget and a result destination that aliases the retained scalar.
- `buffer_survives` and `all_consumed`: the ambient target buffer is unchanged;
  both child boxes and the parent shell are dead at the concrete endpoint.
- `recursive_walk`: an operational regression with a nonempty left child in
  the same program, taking exactly 40 ticks, with ordered frees
  `[4,1,2,5,3]`. This extra fixture is a target execution test, not an additional
  source-context integration proof.

## Scope and remaining gaps

The generic theorem starts at an already established Node-body boundary.
Entry/body/installed-finish integration is closed for the concrete fixture,
not yet a parameterized Case linker or arbitrary recursive Case theorem.
The existing installed-finish theorem composes with the new generic body;
there is no assumed finish execution in the closed integration.

The graph proved here is the explicit body graph, not a full enclosing source
Case graph. `Supported` in the frozen composition contract still excludes drops;
no recursive compiler provider or extension of that subset is claimed. Other
resource inventories, buffer effects, arbitrary case placement/renaming, full
compiler lowering, native semantics and source/target trace equality remain out
of scope. The final scalar local relation is not a function-return ABI theorem.

## Validation

Lean 4.34.1, `-DwarningAsError=true`:

```
LEAN_PATH=proofs/.lake/build/lib/lean lean -DwarningAsError=true \
  -o proofs/.lake/build/lib/lean/Jihoo/CommonCaseChildTransfer.olean \
  proofs/Jihoo/CommonCaseChildTransfer.lean
LEAN_PATH=proofs/.lake/build/lib/lean lean -DwarningAsError=true \
  proofs/Jihoo/CommonCaseChildTransferChecks.lean
```

The existing `CommonCaseChildConsumptionChecks.lean` and
`CommonLiteralFinishChecks.lean` were also rerun with warnings as errors.
Unchanged dependency oleans were reused from the base worktree (which links
some dependencies to the literal/finish integration worktree). This is targeted
validation, not a clean whole-library build. The checks print 14 axiom audits;
all contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
There are no added axioms, `sorry`, `admit`, or native-decision trust extensions.
