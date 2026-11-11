# Symbolic typing to structural MIR construction

This continues `9b442e7f59f9bca6ebfc4083cff439cfe798dabe` on a separate
worktree originally based on main `6703d2e`, rebased onto `cd39f24`. It does not modify CommonData or shared
integration files.

## Source-to-compact representation connection

`SymbolicMirStructuralBridge.typing_erases_typed` proves simultaneously that the
original symbolic source graph erases to a compact term and that this term has
`SizedMir.Structural.Typed`. All ten constructors of the current symbolic
judgment are covered, including both conditional arms, natural applications,
owner transfer, allocation, release and scalar lends. The original symbolic
judgment still has no owned-lend constructor; this does not add one.

`KindsSupport` relates each live source slot to its representation at the
computed retained-slot rank. Proof binders disappear; consumed/transferred dead
aliases keep their runtime slots. Dead slots can also be absent, as permitted
by existing source agreement. Result renaming and dependent substitution do not
change runtime representation kinds.

`typing_compiles_closed` derives the mask and representation relation from the
existing closing-context and environment-agreement hypotheses. Its conclusions
are a fixed typed compact term, successful computed compaction for every
sufficient fuel, and successful `Linear.compile` at every local/block base and
exit, with exact local and block counts. Operand length equality remains
explicit. It does not assert that arbitrary equal-length operands have matching
MIR types.

There is no source execution, successful compaction, MIR compilation, validator
acceptance or checked-entry success premise in this theorem.

## Statement and ABI gates

`SizedMirStructuralBudgets` proves exact statement counts for every compact
constructor, including owned lends. Allocation contributes 11 statements, a
read 2, an owned lend 13, and a conditional 3 plus both arms. These are static
code sizes, not execution costs. The count is at most twice the local cost;
therefore a 512-local budget implies the 4096-statement bound, including the
entry/return wrapper's one statement.

`entry_signature_valid` derives `entryValid` after scratch storage is appended
from distinct nonzero argument slots with declared supported scalar types.
It does not prove runtime argument-value admission or allow pointer arguments.

## Validation and integration

Direct Lake targets cover the new modules and the previous structural
counterexamples. `SymbolicMirStructuralChecks` applies the generic theorem to
the existing branch/lend source derivation and a dependent owned-result
application, and checks erased-proof ranks and absent dead slots.

Shared `proofs/Jihoo.lean`, `proofs/Audit.lean`, audit-count scripts and central
status/roadmap documents are intentionally untouched. Integration must add the
new module imports and public theorem audits, plus the preceding structural
modules if not already included. The checked-entry result below supersedes the open gates recorded in
`SIZED_MIR_STRUCTURAL_TOTALITY.md`, which describes the preceding commit.

## Generated-code validity and checked entry

`SizedMirStructuralValidity.typed_fragment_valid` proves that every generated
block, including both branch arms, passes the MIR statement/terminator checks,
and that the result operand has the declared representation. It uses explicit
ambient operand typing and fragment placement, not `valid code` or execution.
Natural let operands, scalar operands, allocation's six blocks, read, release,
owned read/allocation and typed branch joins are all covered.

`Typed.entry_total` constructs a successful `Entry.lowerProgram` result from a
scalar structural derivation, typed initial operands, `InputsBefore`, return
slot zero typed i64, 512-local/block limits, and distinct nonzero supported
scalar argument slots. The statement budget follows from the cost theorem.

`Typed.entry_admission_total` additionally constructs the actual `entryFrame`
from an explicit per-argument relation: declared type equals value type and
`argumentValueValid` holds (machine-width scalar values). This is an input-value
condition, not an assumed binding operation or target state.

`SymbolicMirLoweringTotality.typed_lowering` constructs one fixed compact term
and sufficient fuel from symbolic source typing, then derives checked lowering,
MIR validity and static ABI validity under the explicit code-size bounds.
`typed_source_total` additionally derives actual ABI admission and specializes
the existing symbolic execution theorem. Successful compaction, lowering,
validation, argument binding and target execution are all conclusions. It
retains closing/inventory agreement, empty initial heap ownership/layout,
input type/width/slot conditions, syntactic storage budgets, and abstract
runtime resource bounds. The storage premise quantifies only over structural
erasures and numerical local/block costs; it is not a compilation certificate.

The old shared `SymbolicMirEntry` theorem still exists unchanged. Integration
can migrate callers to this new theorem or compose the produced witnesses with
the existing all-fuel adequacy theorem. This change proves total execution;
it does not duplicate the all-fuel adequacy conclusion in the new wrapper.

## Remaining boundaries

No CommonData extension, new symbolic owned-lend rule, arbitrary full-Core
coverage, external pointer ABI, pre-existing heap, negative I64 argument model,
native compiler/exporter correctness, LLVM lowering or allocator-realization
claim is added. Abstract runtime resource bounds remain essential. These are
scope boundaries, not hidden success hypotheses. The compact structural
validity theorem itself does cover owned lends.

Validation: all new modules were kernel-checked with Lean 4.34.1. The 15 public
axiom reports in `SymbolicMirStructuralChecks` contain only `propext`,
`Classical.choice` and `Quot.sound`; no `sorryAx` or custom axioms. The original
structural counterexamples also pass. A fresh dependency-closure Lake build was
performed before the final direct module checks. Native compiler tests are not
claimed because production compiler code is unchanged.
