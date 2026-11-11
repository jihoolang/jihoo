# Resource-partitioned common Data application

The 0.6 roadmap requires specified typing rules to supply runtime ownership
and borrow-safety preconditions. Adding another concrete source snapshot does
not establish that composition. This change removes the common Data
application rule's whole-inventory restriction: its argument may consume only
part of the current Data/Buffer inventory while its body retains the rest.

## General rule and runtime interpretation

`CommonData.Typing.dataLetSplit` is a constructor of the existing judgment,
not a separate resource calculus or a fixture certificate. It recognizes the
same direct non-erased App/Lam with fixed binary `Ind(0, [])` domain as the
previous rule. Its explicit static plan partitions the Data slots into an
active prefix and retained suffix, and independently partitions Buffer slots
and their length list. Counts and length-list concatenation must match the
input judgment. Both argument and continuation are recursively typed by the
same judgment; the continuation may return scalar or Data.

`argumentContext` hides every retained capability alias and densely renumbers
the selected Buffer prefix after the selected Data prefix. `capturedContext`
adds the actual returned Data result, revokes every consumed alias and moves
the retained slots behind the result. Nat/scalar/ghost entries and old lexical
positions remain unchanged. The runtime environment does not delete old values.
The partition is over logical capability positions, not allocation footprints:
even two empty trees occupy separate slots. General disjointness lemmas exclude
simultaneous argument/body authority for the same original Data or Buffer slot.

`rel_argument`, `rel_captured` and their environment versions interpret those
static transformations against actual trees, Buffer identities and lexical
values. This is a resource-sensitive binding rule, not general dependent
substitution or a renaming of unrestricted pure typing.

The operational semantics is unchanged: the rule uses `Eval.dataLet`, which
knows neither the partition nor a supplied tree witness. The argument executes
with the existing environment; its actual returned root is bound to the body.
The general `Typing.total` proof obtains the returned tree interpretation from
the argument postcondition, restores the retained interpretations, and applies
the body's induction hypothesis. Safe steps and successful termination are
conclusions, not typing premises. Determinism remains unchanged, so existing
`Typing.every_run` covers the new rule and is independent of a chosen plan.

## The missing frame property

The previous postcondition preserved frame ownership but did not state that
its recursive fields or Buffer lengths survived. Ownership alone cannot justify
using a saved tree's old interpretation after an arbitrary heap computation.

The new frame lemmas derive the needed facts from execution:

- `sized_lengths_frame` and `Eval.lengths_frame`: lengths change only at
  identities named by allocation events.
- `Eval.cells_frame`: recursive cells change only at Data allocations or
  actual release events, including recursive Drop and delayed Case release.
- `surviving_untouched`: in a safe trace, an initially allocated identity that
  remains live was neither freshly allocated nor released. This uses the
  existing monotonically fresh abstract identities and no-resurrection theorem.
- `Eval.frame_fields` reconstructs retained finite-tree `Represents` facts;
  `Eval.frame_layout` restores retained Buffer lengths.
- `Typing.total_preserving` and `Typing.every_run_preserving` strengthen the
  common theorem for **all** derivations with actual cell/length equality on
  every external-frame identity, including nested partitioned applications.

No per-body successful-run, untouched-trace or preserved-field hypothesis is
introduced into the typing rule. Full exact-use trace accounting is not assumed
and is not established by these frame lemmas.

## Production relationship and limits

Production `Core.infer` checks App against a Pi domain and substitutes the
argument into the codomain; `Core.uses` separately sums uses in runtime arguments
and the directly executed lambda body. An unrelated capture can remain available
in the body, but a consumed argument cannot also be used there. The new rule
models that resource distinction for this existing restricted fragment.

It does not mechanize production `Core.infer`/`uses`, dependent Pi substitution,
conversion, general closures, arbitrary partition inference, recursive functions,
general families/motives, Back, native representation or lowering. The Data
model is finite binary trees with abstract non-reused identities and independent
field cells; native boxed Nil, field bytes and shell reuse remain different.
`CommonDataSource.entry` still recognizes its existing single-Tree source entry;
this change does not extend that adapter to infer captured-resource partitions.

The new regression graphs are hand-written tests of the **general rule**,
not claimed production exports. They exercise retained-tree reconstruction and
Drop, arbitrary Buffer sizes split between argument and body, application under
a pending Case shell, scalar/natural/ghost preservation, empty logical slots,
and rejection of reserved/consumed aliases. Existing checked-source snapshot
association remains in the standalone suite. No native compiler changes or new
native execution theorem are claimed; the full 0.6 gate remains open.
