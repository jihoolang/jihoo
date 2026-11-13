# Restricted copied Case register layout

Base: `c35dcf5779f3c8f9a19724eebc00ea5092682da6` on
`proof/common-case-placement`, following contract
`4a701387a15863e40e0218ae1721697d420451ec`. Both actual commits and their
scope documents were inspected. This separate branch changes no shared CI,
root imports, existing contracts, or other branches.

## Concrete failure

The seven-local copied Node entry overwrites slots 0–5. After an outer Node,
its children occupy 4 and 5. Opening its left child as another Node overwrites
the live outer right sibling in 5. `collision_run` executes exactly 23
(11+1+11) actual interpreter ticks in C's same two-fragment program with a
nonempty prefix, root slot 6, child root slot 4, and arbitrary bounded
suspended callers. The heap stays unchanged, while `sibling_overwritten`
proves slot 5 changes from pointer 2 to pointer 4. `collision_steps` exports
ReferenceCalls.Steps. No source correctness is inferred from this run.

## Narrow solution and exact maximality

This change chooses the justified restricted-layout option; it does not
implement register renaming or save/restore. For the existing copied entries:

* Node retains only slots outside [0,1,2,3,4,5].
* Nil retains only slots outside [0,1,6], allowing the sibling in slot 5.

`safe_iff_uniform` proves this restriction is necessary AND sufficient for
preserving every declared retained local across the exact entry local
transformers, uniformly over arrays of size at least seven and all root/child
IDs. Necessity uses an all-empty seven-local array: each written position
changes. This is the largest **value-independent register frame** for these
transformers. It is not maximality among source-typed reachable programs,
state-sensitive value equalities, alternative ABIs, or ownership layouts.
The array quantification and its limitations are explicit in the theorem.

`RestrictedPlacement` combines C's syntactic Placement in one fixed program
with a live-slot list, explicit coverage of every active lexical binding in
the supplied context, and the slot restriction. `reserved` derives the frozen
reservation predicate. `no_node_layout` proves any active binding mapped to
5 rules out a restricted Node placement: omitting it from the live list
cannot evade the restriction. For A integration, Node must cover the entire
pre-entry context, including selected aliases; Nil must cover removeHead ctx.
This preserves A's conservative contract, even where a stronger entry theorem
could permit more. In particular a selected active Node root in slot 4 also
violates A's reservation; rejecting the sibling alone does not repair this.

`checkedEntry` is an executable proof-API guard: unsafe layouts return none
before invoking walk; accepted Node/Nil entries run the original 11/5 ticks.
`checked_node` and `checked_nil` prove their actual fixed-program execution
and retained-register preservation under the explicit heap-shape, root,
space, placement and stack-bound premises. It is not a target instruction,
production emitter change, runtime branch detector, or source type checker.
Clients must supply the correct branch shape and complete liveness/context.
The unguarded old placement APIs intentionally remain operational facts and
can still execute the demonstrated collision.

## Regressions and integration limits

The checks reject the second Node with retained [5] and reject a lexical
context containing an active slot-5 binding. A Node retaining only [6] runs
and preserves it; this test does NOT assert the omitted sibling was consumed.
A Nil after the outer Node runs and preserves the actual sibling in [5].
`Agrees.trans` permits composition for an unchanged retained set; changing
liveness, source typing, ownership, branch bodies, pending-shell finish and
continuations remain independent proof obligations. No general nested Case
compiler correctness, source Eval, or CommonContext preservation is claimed.

A/B's separate implementations are not dependencies of this patch. It imports
C and the frozen contract; integration may use `safe_reserved` to feed A's
reservation premise, but must supply its remaining context/ownership premises.
C's arbitrary finite placement proof is still required and retained.
After #201 lands, replay the contract, C, and this commit onto the appropriate
main; do not replay copied #201 prerequisites. Shared CI integration is separate.
No merge is performed.

Run with Lean 4.34.1 on PATH:

```sh
bash proofs/check-common-data-case-register-safety.sh
```

This builds the dedicated dependency closure with warnings as errors and
checks the axiom reports for all 18 named new theorems against only propext,
Quot.sound and Classical.choice.

Validation: Lean 4.34.1 dependency build and dedicated check passed (126 build
jobs), followed by a fresh check-module invocation and all 18 axiom audits.
No proof holes or global axioms were added. `git diff --cached --check` passed.
The full shared check.sh was not run; only new isolated modules were changed.
