# Conditional common Case proof integration

Integrated on main `ed709dd8cf03fbfa25a50eb76a6478fe57d8971a` (#201).
Only unique commits 4a701387 (contract), 29b6a409 (A), 761a96a5 (B),
c35dcf57 (C), and bfb89fd0 (register safety) were replayed, in that order.
The old Tree context prerequisites 9d55c3f5 and 7a036efa were not replayed:
#201 already includes them and their root, audit, and CI registrations.
The individual scope documents record their original independent-branch work;
this document describes the combined build and remaining obligations.

## Integrated interface

`CommonCaseIntegration.node_finish` uses the concrete `entryProvider`,
`RestrictedPlacement.reserved`, and `finish_result` to construct the shared
`Transfer` and `FinishResult`. All three segments use exactly `i.program`,
the body starts at exactly `i.nodeOut`, and finish starts at exactly the body
output. `nil_entry` derives the corresponding five-tick transfer with the
surviving-context restriction. Placement, complete lexical liveness coverage,
valid ownership, branch shape, local capacity and stack limits remain explicit.

The root imports all five implementation/check pairs plus the integration
module. The aggregate audit retains all 3,589 existing entries and adds 60.
The dedicated composition script runs all five original audit scripts plus
the combined audit. Both existing CI workflows run it; the Nix lean-proofs
fileset already includes the complete Jihoo directory and aggregate audit.

## Independent soundness review and limits

- A constructs an actual EntryProvider, not a postulated axiom. Its Node
  reservation covers the entire input context, including the selected root
  and aliases, against slots 0–5. Thus an active selected root in slot 4 is
  also rejected. Nil covers removeHead ctx against slots 0, 1 and 6.
- B independently proves ownership/resource preservation when a pending shell
  is retired, even with stale child references. It still requires BodyResult
  (typing, source Eval, target Transfer, postcondition and result local) and
  FinishExecution (actual installed walk, exact heap retirement, unchanged
  locals and callers). The concrete free regression works because the unit
  destination already contains unit; it is not a general finish emitter.
- C installs arbitrary finite lists of seven-block fragments in one program
  and proves entry walks and one forward jump. Its induction theorem is an
  eliminator whose step is supplied, not a recursive body-correctness proof.
  The Node-to-Nil example proves target execution; it does not establish
  source/compiler correspondence or a complete return convention.
- Register safety proves an exact uniform restriction on declared retained
  slots for the existing entry transformers. Coverage connects that list to
  active lexical bindings. It does not infer liveness, rename registers,
  save/restore values, or prove maximality for source-typed reachable states.
  The 23-tick Node-to-Node collision remains a useful negative regression.
  Unguarded placement execution is intentionally still possible.
- `Transfer` preserves the boundary context conditionally and fixes callers
  and ambient reservations, but is a running-state prefix certificate.
  `node_finish` supplies no halting/return ABI and no source/target event
  equality. Boxed Nil and allocation events already require a richer trace
  relation. `Supported` alone grants neither typing nor ownership.

No full compiler correctness theorem is claimed. Remaining work includes
constructing body and finish execution providers for real emitted code,
recursive safe register allocation, source typing/ownership induction,
result/return conventions and the appropriate observable trace relation.

## Validation commands

With the pinned Lean 4.34.1 available:

```sh
bash proofs/check-common-case-composition.sh
bash proofs/check.sh
python3 scripts/check_nix_sources.py --offline --system x86_64-linux
```

The first two reject warnings and audit elaborated dependencies against only
`propext`, `Quot.sound`, and `Classical.choice`. Clean validation means a fresh
worktree without inherited `.lake` artifacts; aggregate checking then reuses
only artifacts built in that worktree.
