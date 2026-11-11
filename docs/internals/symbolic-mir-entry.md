# Symbolic typing through checked MIR entry

This layer connects the constructor-driven [symbolic Buffer typing judgment](symbolic-core-typing.md)
to [checked entry and execution adequacy](mir-entry-adequacy.md). It keeps the
source graph unchanged and uses the existing computed ghost-slot compactor and
Lean-generated MIR lowerer.

It is a composition of proved interfaces, not a new claim of full Core or native
compiler correctness. The executable native compiler remains outside the generic
lowering theorem.

## Compaction exists before execution

`SymbolicCoreCompaction.typing_compiles_closed` proves that a symbolic typing
derivation, a closing context and a matching source environment determine a
compact term and a sufficient traversal-fuel threshold. Every larger fuel value
makes the existing `compileTarget` return that same term. No successful source
execution, target execution or safety trace is a premise.

The proof covers every constructor of the current symbolic typing family. It
constructs the existing erasure relation and uses completeness of the existing
fuel-bounded compactor. This supplies the successful-compaction equality used by
the entry interface below; it does not replace the compiler with a different
translation or add a new source admissibility judgment.

The mask condition is derived from the actual computed environment mask. Live
natural, scalar and owner slots are retained, and proof slots are erased. Dead
slots are deliberately unconstrained: consumed or transferred aliases can still
occupy runtime positions, and erasing them would change later lexical ranks.
No extra equality between context and environment lengths is assumed.

This is compactor totality for the symbolic source subset, not successful MIR
lowering for every typed graph. A compact term may still exceed the lowerer's
budgets or have an unsupported target result shape. The following ABI and
resource conditions also remain separate.

## Generic interface

`SymbolicMirEntry.typed_source_total` takes a symbolic typing derivation and its
closing context and inventory interpretation. `Typing.instantiate` produces the
existing sized source judgment on the same graph. The checked-entry theorem then
constructs a source execution and a terminating generated MIR execution.

The following premises remain visible:

- The symbolic context closes to the concrete context, and its inventory
  expressions interpret to the concrete inventory.
- The source environment agrees with that context, with the required initial
  ownership and layout. The initial heap is empty.
- The computed ghost mask successfully compacts the selected source root.
- The compact term successfully lowers within the checked program budgets.
- The real checked argument-binding operation admits the compacted arguments.
- Every source execution has the explicit abstract resource bounds required by
  the target memory model.

There is no separately supplied per-input sized typing derivation, manually
constructed target local state, control-state reset, or assumed target run.
The entry theorem keeps compaction and lowering equalities explicit. The
compactor-totality theorem supplies the former after choosing sufficient fuel;
successful MIR lowering remains an independent condition.

The result includes source execution, generated MIR termination, completed-return
heap correspondence, source ownership accounting, bounded scalar results and
preservation of input locals other than the return slot.

`typed_source_adequacy` additionally proves progress and exact suffix completion
for every reachable running prefix, partial interpreter success for every fuel
budget, exact execution with sufficiently large fuel, and agreement of every
returned execution. The sufficient fuel bound is existential, not a closed-form
runtime cost formula. `typed_source_return` recovers a safe source execution and
ownership account from an observed target return under the same explicit
premises.

## One static dependent Buffer derivation

`SymbolicMirEntryExamples` applies that interface to the retained original
`DependentBufferGraph` body at node 40. Its source derivation is
`SymbolicCoreExamples.body_typed`, which has no length or index parameter. Both
comparison branches are checked before runtime values are supplied.

One generated program and one entry signature serve all inputs satisfying:

- Buffer length `n ≤ 4095`, including zero.
- Index `i < 2^64`; the comparison selects the read or fallback branch.
- Nonnegative scalar payload `value < 2^63`.

The scalar/index/length argument sequence is bound to slots 3/2/1, leaving slot 0
for the return value. Admission is proved for every such input. A length of
4096 is still width-valid at the ABI but exceeds the target resource limit once
the spare cell is included; separate regressions preserve this distinction.
Callers do not
prefill scratch locals or move the admitted frame to a different block.

The universal `total` theorem constructs the source and generated executions.
The returned scalar is the payload when `i < n`, and 99 otherwise. The target
lifecycle is one allocation of `8 * n + 8` bytes followed by release of that same
object. The extra cell is part of the existing abstract allocator convention.
The theorem also gives the exact source events and final state, safe source
steps, final validity, generated final heap correspondence, ownership release
accounting, no live source objects and preservation of argument locals.

`adequacy` gives all-fuel partial interpretation and eventual exact execution for
that admitted program. `observed_return` proves that any observed return from an
admitted frame has the same result, lifecycle, represented heap and source
account. The generated code is fixed; this is not a separate compile-and-prove
exercise for each numeric input.

## Retained native snapshot boundary

`generated_and_retained_native` compares the generated program with the existing
`DynamicMir` snapshot for the same parameters. Both use their own real checked
entry, and both terminate with the same scalar and allocation/release sequence.
The generated final heap represents the source heap; the retained native
snapshot has no live objects on return.

The external regression establishes which native source/exported fixture this
snapshot represents. No theorem verifies the general native compiler exporter,
MIR-to-LLVM translation, machine execution, physical pointer identities or real
allocator success. Internal source leases/reads and MIR initialization stores
are not equated. Heap correspondence is asserted at completed return, not at
every partial initialization step.

## Remaining scope

The generic result covers the current symbolic source judgment and supported
compact scalar-result programs. It excludes external pointer arguments,
pre-existing heaps, negative I64 payloads and arbitrary full-Core programs. It
does not remove resource bounds, prove every source program lowers, or close the
original 0.6 release gate.
