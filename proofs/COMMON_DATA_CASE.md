# A common judgment for binary Case reconstruction and Buffer effects

`CommonData.Typing` and `CommonData.Eval` put actual empty/node Case selection,
linear data return/construction and existing sized scalar Buffer bodies in one
judgment and one operational relation. Unlike the earlier body segment, a
completed Data result owns a represented tree rather than returning a separate
residual child inventory. The concrete reconstruction example proves that both
original subtrees belong to that returned tree.

## Source and existing Core boundary

`CommonData.Graph` is an explicitly restricted extension of the existing
`ScopedLend.Graph` view. Core nodes keep their indices. New nodes are empty,
binary construction, Case and an explicit embedded scalar-Core entry point.
`core_at` proves the index-preserving projection; extension nodes project to
opaque. A Buffer scalar let uses the existing application/lambda/i64 shapes,
runs its argument under `SizedCoreTyping.Typing`, then checks its continuation
in the common judgment with all Buffer aliases retired and Data roots retained.
The explicit embedded node disambiguates the old-Core execution boundary from
the common let rule. These are hand-built proof graphs, not production exporter
snapshots or new compiler syntax. `validGraph` checks size and backward edges;
old Core numeric/typing restrictions still come from its typing premises.

Typing tracks a Data prefix followed by a Buffer suffix. Empty return requires
no capabilities, variable return exactly one Data capability, and construction
exactly two distinct Data slots and no Buffers. Case checks a variable scrutinee
at the head capability, both branches at the same result kind, and their whole
remaining inventories. Empty removes that capability. Node reads actual stored
child roots, binds right/left/erased lexical slots, retires every parent alias,
and replaces the head capability with two children. No successful body run is
assumed by the typing rule.

`Typing.total` constructs a run, safe heap steps, a valid final heap and a
`Post` result from typing, lexical agreement, Buffer layout, ownership and field
interpretation. Scalar results retain only the frame; Data results retain one
represented tree disjoint from that frame. `scalar_total` derives the existing
Core execution and recombines Data and pending-frame ownership. Buffer segments
freeze the abstract cell store; construction writes a fresh cell and Case
clears the old parent cell after the body. `Post.finish` proves that this final
release preserves the returned tree, including its field interpretation.
`Eval.deterministic` and `Typing.every_run` extend the result to every admitted
execution. The theorem is parametric in an arbitrary pending ownership frame. Its `Post`
asserts positive ownership and representation, not exhaustive heap ownership.
A generic common-judgment trace accounting theorem (every input/new allocation
is released or returned) remains open; the old Buffer accounting used internally
does not by itself establish that stronger claim for the entire common language.

## What remains open

This is a common judgment for a **monomorphic binary reconstruction fragment**,
not the full common-Core release gate. It supports arbitrary finite input
subtrees, but no recursive function/body rule, Drop, general data sequencing or
arbitrary constructor telescope. Construction is terminal and takes precisely
two variables, which limits nested Case/reconstruction programs. In particular,
there is no claim that arbitrary trees can be consumed to return a scalar.

Both branches have the same coarse scalar/Data kind; dependent motives,
indexed families, constructor tags and general exhaustiveness are unmodeled.
The field store is an abstract map, not native bytes. Native shell reuse, tag
layout, Case lowering, MIR/LLVM correspondence and allocator behavior remain
unproved. Back/Give/Take and symbolic lengths are not added by this change.
No production compiler code or shared common-Core audit is changed.

## Validation

The nonempty fixture consumes Buffers 4 and 5, allocates/lends/reads/frees Buffer
7, constructs Data root 8 pointing to original children 1 and 2 (including
descendant 3), and releases old parent 0 last. Its final owned inventory is
`[8,1,2,3,6]`, with external frame 6 retained. The same typed Case on empty input
executes its empty branch, frees both Buffers and returns empty. Concrete initial
validity, layout, field interpretation, execution and final ownership are proved.

Negative checks reject repeated construction children, dropped children,
unconsumed Buffers, a scalar constructor result and missing field cells. Slot
shift and duplicate-parent retirement checks accompany an old-Core embedding
example and an opaque projection regression. Run
`bash proofs/check-recursive-fields.sh` or the independent Nix
`recursive-field-proofs` check; see [the overview](RECURSIVE_FIELDS.md) for the
complete axiom-audit count.
