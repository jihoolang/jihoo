# Checked MIR entry and execution adequacy

This result connects the existing restricted sized-Core typing and erasure
pipeline to an actual checked entry frame for generated Lean MIR. It also states
what every finite execution prefix and every returned execution guarantees.
It does not extend the specified source language or prove the native compiler.
See the [Lean proof boundary](lean-proofs.md) and the
[0.6 release blocker](0.6-proof-status.md) for the remaining common-typing work.

## A real entry block

The earlier generated programs have a return block at index zero. Their
simulation theorem starts at the fragment's computed entry, with an explicitly
related frame. That is a valid internal execution interface, but it is not a
program that the scalar `entryFrame` API starts directly at block zero.

`SizedMirEntryProgram` provides a separate constructor:

- Block zero jumps to the computed fragment entry.
- Block one copies the result into return local zero and returns it.
- Generated fragments begin at block two and continue to block one.
- An instruction-free term jumps directly to the return block.

The compiler checks the entire completed code, including the entry wrapper,
with the existing local, block and statement limits. Argument slots must belong
to the original input declarations, not generated scratch storage. The program
executes the admitted frame itself. The proof does not reset its control state,
append locals afterward, prefill scratch values, or assume a successful MIR run.

## What admission establishes

`SizedMirEntryArguments` proves properties of the existing `bindArguments` and
`entryFrame` functions, rather than replacing their checks. Distinct-slot binding
retains every argument value and declaration despite later writes to other slots.
Successful admission then derives:

- Each compact environment entry is represented by the corresponding ordered
  operand, even when argument slots are not numerically sorted.
- Declared operand kinds match the actual represented values.
- Natural and nonnegative scalar values fit the modeled machine widths.
- The frame has the complete declaration count, starts at block zero and
  statement zero, and has an empty heap.

Duplicate slots, return-slot arguments, missing declarations, wrong arity,
wrong value types and out-of-range values remain rejected. External pointers,
addresses and pre-existing heaps are not admitted. The compact interface has
natural and scalar external values; internal allocations and branches can still
produce and transfer owned pointers. This is not an FFI ownership theorem or a
model of negative signed arguments.

## Source-facing guarantee

The source wrapper computes the ghost-slot mask and compact environment with
`compactEnv`. It uses the existing structural graph compactor, generated MIR
compiler and `SizedCoreTyping.Typing` interpretation. The caller no longer
supplies separate erasure-environment, MIR-environment, representation-kind,
frame-size or initial heap-relation proofs.

The remaining premises are explicit:

- Successful whole-syntax source compaction and checked MIR lowering.
- The existing source typing derivation and its context, layout and ownership
  interpretation over the empty initial heap.
- Successful checked admission of the computed compact arguments.
- Source resource adequacy: every source execution's final allocated identities,
  cumulative cells and payloads satisfy the bounded heap model.

From these, `typed_source_total` constructs both the source execution and the
terminating generated MIR execution. It preserves the exact final heap relation,
source ownership accounting, modeled scalar width, and original input locals
other than the return slot. No target execution is a premise of totality.

The unchanged sized-composition Core graph at root 81 instantiates this wrapper
for arbitrary admitted inputs. Both original comparisons remain present. The
example proves admission under the capacity/index/payload bounds, then obtains
execution, exact heap correspondence and accounting through the generic wrapper.

## Every prefix and every return

`BoundedMirExecutionAdequacy` uses relational step determinism. Given a
terminating relational execution, every reachable finite prefix has an exact
remaining event suffix leading to the same final machine. Every reachable
running state has a next step and a successful `rawTick` result.

The proof-free interpreter implements every relational step. Consequently:

- `runFor` succeeds for every fuel budget, possibly returning a partial running
  state when the budget is small.
- Enough fuel makes `runFor` return the exact final value, frame and events.
- Enough fuel makes `execute` return that same outcome. A smaller `execute`
  budget may time out; timeout alone does not mean the program is stuck.

`SizedMirEntryAdequacy` obtains the required terminating run from source typing
and totality. Its observed-return corollary supplies an actual source execution,
a safe source trace, valid final source state, exact lifecycle observation,
related returned heap, ownership accounting and scalar bound for every target
return. It does not recover erased lease events from MIR alone: source execution
and its determinism provide that witness.

Heap correspondence is stated at the completed return. An intermediate
allocation loop may contain partially initialized objects, so the result does
not silently assert the full source heap relation at every instruction.

## Tests and limits

Kernel-checked regressions start directly from checked entry frames, with no
manual block change. They cover empty and permuted argument lists, ghost slots
removed by compaction, both comparison outcomes, allocation and release,
empty/zero-copy/nonempty paths through the original Core graph, and ABI rejection
cases. Separate tests distinguish a short successful execution prefix from
`execute` timeout and a genuinely stuck malformed program.

These are generic results for the supported Lean-generated compact programs
and deterministic bounded MIR semantics. They do not turn the retained native
fixture correspondence into a generic `core_lower.jh` refinement proof. Broader
source typing, arbitrary lender bodies, native ABI association, physical machine
addresses, allocator failure, MIR-to-LLVM and LLVM remain outside the result.
The broader 0.6 release gate remains open.
