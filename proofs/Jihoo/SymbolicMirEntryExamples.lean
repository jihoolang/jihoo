import Jihoo.SymbolicMirEntry
import Jihoo.SymbolicCoreExamples
import Jihoo.SizedMirEntryExamples
import Jihoo.SizedMirLendExamples
import Jihoo.SizedMirLinearExamples
import Jihoo.DynamicMirCorrespondence

/-! One static source derivation and one generated program cover the unchanged
root-40 dependent-buffer graph. Numeric bounds discharge real ABI admission and
abstract allocation limits; callers never prefill locals or reset control. -/
namespace Jihoo.SymbolicMirEntryExamples
open BoundedMir SizedMir
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

abbrev term := DynamicMirCorrespondence.target
def types : Array Ty := #[.i64,.u64,.u64,.i64]
def abi : BoundedMir.Entry := ⟨#[3,2,1]⟩
def fragment : Linear.Fragment := SizedMirEntryExamples.fragment types abi term
def code : Code := Entry.program types term fragment

theorem lowered : Entry.lowerProgram types abi term = some fragment := by decide +kernel

theorem compacted : SizedErasure.compileTarget DependentBufferGraph.graph 128
    (SizedErasure.compactEnv (SizedCoreExamples.inputEnv n i value)).1 40 = some term :=
  DynamicMirCorrespondence.compiled

/-- The runtime order is scalar/index/length; the ABI slots reverse it. Even
equal-typed natural arguments are placed by checked binding, not a frame axiom. -/
theorem admission (capacity : n ≤ 4095) (index : i < wordBound)
    (payload : value < scalarBound) :
    ∃ f, entryFrame code abi [.i64 value,.u64 i,.u64 n] = some f := by
  have hn : n < wordBound := by unfold wordBound; omega
  have signature : entryValid code abi = true := Entry.lowerProgram_entryValid lowered
  have size : code.locals.size = 20 := by decide +kernel
  have t1 : code.locals[1]? = some .u64 := by decide +kernel
  have t2 : code.locals[2]? = some .u64 := by decide +kernel
  have t3 : code.locals[3]? = some .i64 := by decide +kernel
  unfold entryFrame
  rw [signature]
  change ∃ f, bindArguments code [3,2,1] [.i64 value,.u64 i,.u64 n] (initial code) = some f
  simp [bindArguments, argumentValueValid, valueType, initial, size, t1, t2, t3,
    hn, index, payload, Array.set!, Array.setIfInBounds]
  obtain ⟨_, e3⟩ := Array.getElem_of_getElem? t3
  obtain ⟨_, e2⟩ := Array.getElem_of_getElem? t2
  obtain ⟨_, e1⟩ := Array.getElem_of_getElem? t1
  exact ⟨e3,e2,e1⟩

theorem final_bounds (capacity : n ≤ 4095) (payload : value < scalarBound) :
    Trace.Bounds (SizedCoreExamples.bodyFinal n i value) := by
  unfold SizedCoreExamples.bodyFinal
  split
  · exact SizedMirLendExamples.source_bounds capacity payload
  · exact SizedMirLinearExamples.source_bounds capacity payload

theorem every_run_bounded (capacity : n ≤ 4095) (payload : value < scalarBound)
    (run : SizedCoreExecution.Eval DependentBufferGraph.graph (SizedCoreExamples.inputEnv n i value)
      40 SizedBufferHeap.empty result events t) : Trace.Bounds t := by
  rw [(SizedCoreExamples.every_run_exact run).2.2]
  exact final_bounds capacity payload

theorem body_lifecycle : lifecycle (SizedCoreExamples.bodyEvents n i value) =
    [.alloc 0 (n * 8 + 8),.free 0] := by
  by_cases h : i < n <;>
    simp [SizedCoreExamples.bodyEvents, SizedCoreExamples.readEvents, lifecycle, h]

/-- Symbolic instantiation supplies source totality and safety. Determinism
identifies its exact source result/trace/heap; checked lowering constructs MIR
termination, with an exact lifecycle projection and release accounting. -/
theorem total (capacity : n ≤ 4095) (index : i < wordBound)
    (payload : value < scalarBound) :
    ∃ f final,
      entryFrame code abi [.i64 value,.u64 i,.u64 n] = some f ∧
      SizedCoreExecution.Eval DependentBufferGraph.graph (SizedCoreExamples.inputEnv n i value) 40
        SizedBufferHeap.empty (.scalar (if i < n then value else 99))
        (SizedCoreExamples.bodyEvents n i value) (SizedCoreExamples.bodyFinal n i value) ∧
      SizedBufferHeap.Steps SizedBufferHeap.empty (SizedCoreExamples.bodyEvents n i value)
        (SizedCoreExamples.bodyFinal n i value) ∧
      SizedBufferHeap.Valid (SizedCoreExamples.bodyFinal n i value) ∧
      Steps code (.running f) [.alloc 0 (n * 8 + 8),.free 0]
        (.returned (if i < n then value else 99) final) ∧
      HeapRel (SizedCoreExamples.bodyFinal n i value) final.heap ∧
      SizedCoreTyping.Account [] (.scalar (if i < n then value else 99))
        (SizedCoreExamples.bodyEvents n i value) ∧
      (if i < n then value else 99) < scalarBound ∧
      (∀ x, (SizedCoreExamples.bodyFinal n i value).heap.live x = false) ∧
      final.locals.size = code.locals.size ∧
      (∀ k, k < types.size → k ≠ 0 → final.locals[k]? = f.locals[k]?) := by
  have hn : n < 2^64 := by omega
  obtain ⟨f, admitted⟩ := admission capacity index payload
  have closing := SymbolicCoreExamples.inputs_close hn index
  obtain ⟨result, events, state, final, source, target, heap, account, bound, size, retained⟩ :=
    SymbolicMirEntry.typed_source_total compacted lowered SymbolicCoreExamples.body_typed
      closing .nil (SizedCoreExamples.input_agrees n i value) SizedCoreExamples.empty_layout
      LinearHeapPrograms.empty_owns
      (by simpa [code, SizedCoreExamples.inputEnv, SizedErasure.compactEnv, toMir] using admitted)
      (fun _ _ _ run => every_run_bounded capacity payload run)
  obtain ⟨same, ev, st⟩ := SizedCoreExamples.every_run_exact source
  cases same
  subst events state
  have safe := ((SymbolicCoreExamples.body_typed.instantiate (resultKind := .scalar) closing .nil trivial).every_run_safe
    (SizedCoreExamples.input_agrees n i value) SizedCoreExamples.empty_layout
    SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns source).1
  exact ⟨f, final, admitted, source, safe, SizedBufferHeap.steps_valid SizedBufferHeap.empty_valid safe,
    by simpa [code, body_lifecycle] using target, heap, account, bound,
    SizedCoreExamples.body_final_no_live n i value, size, retained⟩

/-- Fuel bounds are existential, not a claimed closed-form cost model. Every
budget has a partial result, and sufficiently large budgets return exactly. -/
theorem adequacy (capacity : n ≤ 4095) (index : i < wordBound)
    (payload : value < scalarBound) :
    ∃ f final,
      entryFrame code abi [.i64 value,.u64 i,.u64 n] = some f ∧
      HeapRel (SizedCoreExamples.bodyFinal n i value) final.heap ∧
      (∀ fuel, ∃ out, runFor fuel code (.running f) = some out) ∧
      (∃ bound, ∀ fuel, bound ≤ fuel → execute fuel code f =
        some ⟨(if i < n then value else 99),final,[.alloc 0 (n * 8 + 8),.free 0]⟩) ∧
      (∀ actual actualEvents actualFinal,
        Steps code (.running f) actualEvents (.returned actual actualFinal) →
        actual = (if i < n then value else 99) ∧ actualFinal = final ∧
        actualEvents = [.alloc 0 (n * 8 + 8),.free 0]) := by
  obtain ⟨f, final, admitted, _, _, _, target, heap, _⟩ := total capacity index payload
  exact ⟨f, final, admitted, heap, target.runFor_total, target.execute_complete,
    fun _ _ _ observed => observed.returned_deterministic target⟩

/-- An externally observed return from any admitted frame has the exact
source scalar, allocator lifecycle, final heap relation and release account. -/
theorem observed_return (capacity : n ≤ 4095) (index : i < wordBound)
    (payload : value < scalarBound)
    (admitted : entryFrame code abi [.i64 value,.u64 i,.u64 n] = some f)
    (observed : Steps code (.running f) actualEvents (.returned actual actualFinal)) :
    actual = (if i < n then value else 99) ∧
      actualEvents = [.alloc 0 (n * 8 + 8),.free 0] ∧
      HeapRel (SizedCoreExamples.bodyFinal n i value) actualFinal.heap ∧
      SizedCoreTyping.Account [] (.scalar actual) (SizedCoreExamples.bodyEvents n i value) ∧
      SizedCoreExecution.Eval DependentBufferGraph.graph (SizedCoreExamples.inputEnv n i value) 40
        SizedBufferHeap.empty (.scalar actual) (SizedCoreExamples.bodyEvents n i value)
        (SizedCoreExamples.bodyFinal n i value) := by
  obtain ⟨expected, final, entry, source, _, _, target, heap, account, _⟩ :=
    total capacity index payload
  have same : expected = f := Option.some.inj (entry.symm.trans admitted)
  subst expected
  obtain ⟨rfl, rfl, rfl⟩ := observed.returned_deterministic target
  exact ⟨rfl, rfl, heap, account, source⟩

/-- This is only a comparison with the retained DynamicMir fixture snapshot.
Its external source/export association is not generic native compiler
verification. Internal leases/reads and initialization stores are not equated. -/
theorem generated_and_retained_native (capacity : n ≤ 4095) (index : i < wordBound)
    (payload : value < scalarBound) :
    ∃ f final dest,
      entryFrame code abi [.i64 value,.u64 i,.u64 n] = some f ∧
      entryFrame DynamicMir.code DynamicMir.entry [.u64 n,.u64 i,.i64 value] =
        some (DynamicMir.inputs n i value) ∧
      Steps code (.running f) [.alloc 0 (n * 8 + 8),.free 0]
        (.returned (if i < n then value else 99) final) ∧
      Steps DynamicMir.code (.running (DynamicMir.inputs n i value))
        [.alloc 0 (n * 8 + 8),.free 0]
        (.returned (if i < n then value else 99) (DynamicMir.finalFrame n i value dest)) ∧
      HeapRel (SizedCoreExamples.bodyFinal n i value) final.heap ∧
      heapEmpty (DynamicMir.finalFrame n i value dest) = true := by
  obtain ⟨f, final, admitted, _, _, _, target, heap, _⟩ := total capacity index payload
  obtain ⟨dest, native⟩ := DynamicMir.terminates (i := i) capacity payload
  exact ⟨f, final, dest, admitted, DynamicMir.input_frame capacity index payload,
    target, native, heap, DynamicMir.final_no_live n i value dest⟩

end Jihoo.SymbolicMirEntryExamples
