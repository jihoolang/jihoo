# Constant-result source Case rules

`CommonDataSourceRules.Typing` gives recursive typing rules over the existing
`CommonDataSource.Node` constructor view. Its Case rule recognizes exactly a
non-erased Tree binder with constant Tree or I64 result. Both branches must have
that result kind and the existing common capability inventories. The node branch
has two non-erased Tree binders, with lexical order right, left, outer bindings.
No graph IDs or variable indices are renumbered.

Unlike the old strict adapter, the nil branch need not be the empty constructor.
It can compute using any derivation of this source judgment. Node branches can
contain nested Case, Drop, direct application and partitioned application. The
constructor rule still accepts two variable operands. Buffer-let arguments reuse
the existing sized scalar judgment over the Core projection: extension nodes,
including Case, project to opaque. There is no unrestricted target-typing escape.

`Typing.elaborate` covers every source rule and yields the existing
`CommonData.Typing` judgment. `Typing.total_accounted` consequently constructs
safe abstract evaluation and the same whole-result allocation accounting as the
common judgment, from its ordinary initial representation and ownership premises.
It does not assume a successful run or a post-body resource interpretation.

The general adapter is deliberately not a source certificate by itself: it
forgets the motive after recognizing its form. A common target typing derivation
alone cannot establish that the original motive agrees with the branch result.
Only the source judgment enforces that condition. `Typing.case_motive` records
this restriction. `CheckedEntry` additionally requires the existing whole-graph
validity and binary-family checks and matches the original direct Tree -> I64 or
Tree -> Tree export annotation to its body judgment. Bare source `Typing` does
not itself assert whole-source or family validity.

## Checks and boundaries

The standalone audit includes scalar Case with recursive destruction, a computed
Data nil arm, nested Case with an outer capture, partitioned source application,
rejected scalar/Data mismatches on both arms, dependent/erased/wrong-domain
motives and branch binders, rejected parent alias reuse, and a rejected export
result annotation. A concrete scalar run releases children 1, 2, 3 and then
parent 0; its accounted postcondition is obtained through source elaboration.

The new source graphs are hand-written regressions. The old strict adapter and
its complete production-checker constructor-view snapshot remain unchanged and
are still checked. This work is source-view typing to **adapted abstract runtime**
safety/accounting, not preservation of an independently defined source evaluator,
a proof of the production checker, or a new compiler export/refinement theorem.
The family remains fixed and binary, motives constant, and applications direct.
Dependent motives/conversion, general families, recursive functions, Back,
logical accounting of empty capabilities, native layout/address reuse and
full-language ownership remain outside this theorem. Allocation-accounting
assumptions and conditional leak-freedom limits remain those of
[common accounting](COMMON_DATA_ACCOUNTING.md).


## Buffer producer/consumer applications

`bufferApp` selects a prefix of the Buffer inventory for any
`SizedCoreTyping.Typing ... (.owner n)` producer. It preserves all Data
capabilities and the remaining Buffer frame, then checks the common consumer
with the returned Buffer prepended. `bufferCall` retains lexical positions,
invalidates every old consumed alias and preserves retained aliases. The runtime
uses the existing `Eval.allocate` rule; there is no new evaluator or assumed
post-state. SizedCore totality, lease framing and exact allocation accounting
establish one returned owner, and the common induction composes the consumer.

The symbolic source rule shifts both the returned length and retained lengths
under the binder. Closing and the independent source evaluator correspondence
feed the existing totality and every-run accounting results. Checks cover a
producer which frees one Buffer and returns another, a retained third Buffer,
Data Case with release in both arms, all suitable symbolic lengths, consumed
and retained-alias rejection, and the old direct Alloc graph through prefix zero.
Only uniform Buffers and direct calls are covered; higher-order closure and
full native compiler verification are not claimed.
