import Jihoo.SizedMirLinearProgram
import Jihoo.SizedErasureExamples

/-! The modeled MIR program is computed from the compacted, unchanged native-
exported Core graph at body root 81. This is not a theorem about the native
core_lower.jh MIR generator or the native ABI. Both source comparisons are retained. -/
namespace Jihoo.SizedMirBranchCoreExamples
open ScopedLend SizedBufferContext SizedCoreTyping SizedCoreExecution DependentBufferIndices
open BoundedMir SizedMir SizedMir.Linear
open SizedCompositionExamples (allocated copied finish)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

abbrev graph := SizedCompositionGraph.graph
abbrev mask := SizedErasureExamples.inputMask
abbrev term := SizedErasureExamples.target
abbrev sourceEnv := SizedCompositionExamples.inputEnv
abbrev env := SizedErasureExamples.runtimeEnv

theorem compacted : SizedErasure.compileTarget graph 128 mask 81 = some term :=
  SizedErasureExamples.compiled

def finalState (n m i value : Nat) : SizedBufferHeap.State :=
  if i < n then
    if 0 < m then finish (SizedBufferHeap.restore (copied n m value))
    else finish (copied n m value)
  else SizedBufferHeap.release (allocated n value) 0

def events (n m i value : Nat) : List SizedBufferHeap.Event :=
  if i < n then
    if 0 < m then
      [.alloc 0 n value, .beginLease 0 0, .read 0 i value,
        .alloc 1 m value, .close 0, .beginLease 1 1, .read 1 0 value,
        .close 1, .free 0, .free 1]
    else [.alloc 0 n value, .beginLease 0 0, .read 0 i value,
        .alloc 1 m value, .close 0, .free 0, .free 1]
  else [.alloc 0 n value, .free 0]

theorem source_run (n m i value : Nat) :
    SizedCoreExecution.Eval graph (sourceEnv n m i value) 81
      SizedBufferHeap.empty (.scalar (if i < n then value else 99))
      (events n m i value) (finalState n m i value) := by
  by_cases readable : i < n
  · simp only [events, finalState, ite_eq_left readable]
    by_cases nonzero : 0 < m
    · simp only [ite_eq_left nonzero]

      apply SizedCoreExecution.Eval.app rfl rfl
        (.allocate rfl (Eval.var rfl rfl) (.var rfl rfl))
      apply SizedCoreExecution.Eval.yes rfl (Eval.var rfl rfl) (Eval.var rfl rfl) readable
      apply SizedCoreExecution.Eval.ownedLend SizedCompositionExamples.copy_shape rfl rfl
        (Eval.var rfl rfl) (Eval.var rfl rfl)
      apply SizedCoreExecution.Eval.app rfl rfl
        (.app rfl rfl (.var rfl rfl) (.var rfl rfl))
      apply SizedCoreExecution.Eval.yes rfl (Eval.literal rfl (by decide))
        (Eval.var rfl rfl) nonzero
      exact .lend SizedCompositionExamples.observe_shape rfl rfl (Eval.literal rfl (by decide))
        (.free rfl rfl rfl (.free rfl rfl rfl (.var rfl rfl)))
    · simp only [ite_eq_right nonzero]

      apply SizedCoreExecution.Eval.app rfl rfl
        (.allocate rfl (Eval.var rfl rfl) (.var rfl rfl))
      apply SizedCoreExecution.Eval.yes rfl (Eval.var rfl rfl) (Eval.var rfl rfl) readable
      apply SizedCoreExecution.Eval.ownedLend SizedCompositionExamples.copy_shape rfl rfl
        (Eval.var rfl rfl) (Eval.var rfl rfl)
      apply SizedCoreExecution.Eval.app rfl rfl
        (.app rfl rfl (.var rfl rfl) (.var rfl rfl))
      apply SizedCoreExecution.Eval.no rfl (Eval.literal rfl (by decide))
        (Eval.var rfl rfl) nonzero
      exact .free rfl rfl rfl (.free rfl rfl rfl (.var rfl rfl))
  · simp only [events, finalState, ite_eq_right readable]

    apply SizedCoreExecution.Eval.app rfl rfl
      (.allocate rfl (Eval.var rfl rfl) (.var rfl rfl))
    apply SizedCoreExecution.Eval.no rfl (Eval.var rfl rfl) (Eval.var rfl rfl) readable
    exact .free rfl rfl rfl (.scalar rfl)

def inputTypes : Array Ty := #[.i64,.i64,.u64,.u64,.u64]
def inputs : List Operand := [.copy ⟨1,false⟩,.copy ⟨2,false⟩,.copy ⟨3,false⟩,.copy ⟨4,false⟩]
def fragment : Fragment :=
  (compile inputs ((inputKinds inputTypes inputs).getD []) 5 1 0 term).getD
    (pureFragment (.constant (.i64 0)))
def code : Code := program inputTypes fragment

theorem lowered : lowerProgram inputTypes inputs term = some fragment := by decide +kernel

def frame (n m i value : Nat) : Frame :=
  ⟨0,0,#[some (.i64 777),some (.i64 value),some (.u64 i),some (.u64 m),some (.u64 n)],
    materialize SizedBufferHeap.empty⟩

theorem related : EnvRel (env n m i value) inputs (frame n m i value) :=
  .keep rfl (.keep rfl (.keep rfl (.keep rfl .nil)))

theorem final_bounds (capacity : n + m + 2 ≤ 4096) (payload : value < scalarBound) :
    Trace.Bounds (finalState n m i value) := by
  unfold finalState
  split
  · split
    · constructor
      · change 2 ≤ 512; decide
      · change cellCount (finish (copied n m value)) ≤ 4096
        simp only [finish, cellCount_release, copied, SizedOwnedLend.final, cellCount_allocate,
          allocated]
        change cellCount (SizedBufferHeap.allocate SizedBufferHeap.empty n value) + m + 1 ≤ 4096
        rw [cellCount_allocate]
        have empty : cellCount SizedBufferHeap.empty = 0 := rfl
        rw [empty]; omega
      · intro objectId old
        change objectId < 2 at old
        have alternatives : objectId = 0 ∨ objectId = 1 := by omega
        rcases alternatives with rfl | rfl <;>
          simpa [finish, copied, allocated, SizedOwnedLend.final, SizedBufferHeap.release,
            SizedBufferHeap.allocate, SizedBufferHeap.restore, restored,
            SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put] using payload
    · constructor
      · change 2 ≤ 512; decide
      · simp only [finish, cellCount_release, copied, SizedOwnedLend.final, cellCount_allocate,
          allocated]
        change cellCount (SizedBufferHeap.allocate SizedBufferHeap.empty n value) + m + 1 ≤ 4096
        rw [cellCount_allocate]
        have empty : cellCount SizedBufferHeap.empty = 0 := rfl
        rw [empty]; omega
      · intro objectId old
        change objectId < 2 at old
        have alternatives : objectId = 0 ∨ objectId = 1 := by omega
        rcases alternatives with rfl | rfl <;>
          simpa [finish, copied, allocated, SizedOwnedLend.final, SizedBufferHeap.release,
            SizedBufferHeap.allocate, SizedBufferHeap.restore, restored,
            SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put] using payload
  · constructor
    · change 1 ≤ 512; decide
    · rw [cellCount_release, allocated, cellCount_allocate]
      have empty : cellCount SizedBufferHeap.empty = 0 := rfl
      rw [empty]; omega
    · intro objectId old
      change objectId < 1 at old
      have same : objectId = 0 := by omega
      subst objectId
      simpa [allocated, SizedBufferHeap.release, SizedBufferHeap.allocate,
        SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put] using payload

/-- Source typing supplies bounds-check and release safety. Only source heap
capacity and payload width are assumptions; the generated run is constructed. -/
theorem generated_run (capacity : n + m + 2 ≤ 4096) (payload : value < scalarBound) :
    ∃ final, Steps code
      (.running (start (programFrame fragment (frame n m i value)) (entry 1 0 term)))
      (lifecycle (events n m i value)) (.returned (if i < n then value else 99) final) ∧
      HeapRel (finalState n m i value) final.heap := by
  obtain ⟨final, target, heap, _⟩ := typed_source_run compacted lowered
    (SizedCompositionExamples.body_typed n m i)
    (SizedErasureExamples.inputs_related n m i value)
    (SizedCompositionExamples.input_agrees n m i value) ⟨rfl, by simp⟩
    SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns
    (f := frame n m i value) rfl related rfl (HeapRel.materialize_related _)
    (source_run n m i value) (final_bounds capacity payload)
  exact ⟨final, target, heap⟩

/-- Every source execution meets the source-only resource bound, by determinism. -/
theorem every_run_bounded (capacity : n + m + 2 ≤ 4096) (payload : value < scalarBound)
    (run : SizedCoreExecution.Eval graph (sourceEnv n m i value) 81
      SizedBufferHeap.empty result es t) : Trace.Bounds t := by
  obtain ⟨_, _, same⟩ := run.deterministic (source_run n m i value)
  rw [same]
  exact final_bounds capacity payload

/-- Original Core typing constructs both total executions with exact scalar
semantics, including the empty-input and empty-copy paths. -/
theorem typed_total (capacity : n + m + 2 ≤ 4096) (payload : value < scalarBound) :
    ∃ es t final,
      SizedCoreExecution.Eval graph (sourceEnv n m i value) 81 SizedBufferHeap.empty
        (.scalar (if i < n then value else 99)) es t ∧
      Steps code (.running (start (programFrame fragment (frame n m i value)) (entry 1 0 term)))
        (lifecycle es) (.returned (if i < n then value else 99) final) ∧
      HeapRel t final.heap ∧ Account [] (.scalar (if i < n then value else 99)) es := by
  obtain ⟨result, es, t, final, source, target, heap, account⟩ :=
    typed_source_total compacted lowered (SizedCompositionExamples.body_typed n m i)
      (SizedErasureExamples.inputs_related n m i value)
      (SizedCompositionExamples.input_agrees n m i value) ⟨rfl, by simp⟩
      SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns
      (f := frame n m i value) rfl related rfl (HeapRel.materialize_related _)
      (fun _ _ _ run => every_run_bounded capacity payload run)
  have same := SizedCompositionExamples.every_run_value source
  cases same
  exact ⟨es, t, final, source, target, heap, account⟩

theorem generated_valid : valid code = true := lowerProgram_valid lowered

/-- Full heap and lifecycle observations, not just the returned scalar. -/
def observe (fuel n m i value : Nat) : Option (Nat × Array Object × List BoundedMir.Event) := do
  let out ← runFor fuel code
    (.running (start (programFrame fragment (frame n m i value)) (entry 1 0 term)))
  let .returned result final := out.machine | none
  return (result, final.heap, out.events)

theorem executable_empty_original : observe 200 0 3 0 42 =
    some (99, materialize (finalState 0 3 0 42), [.alloc 0 8,.free 0]) := by decide +kernel

theorem executable_outside : observe 200 7 2 7 42 =
    some (99, materialize (finalState 7 2 7 42), [.alloc 0 64,.free 0]) := by decide +kernel

theorem executable_zero_copy : observe 200 7 0 6 42 =
    some (42, materialize (finalState 7 0 6 42), [.alloc 0 64,.alloc 1 8,.free 0,.free 1]) := by
  decide +kernel

theorem executable_positive_copy : observe 200 7 2 6 42 =
    some (42, materialize (finalState 7 2 6 42), [.alloc 0 64,.alloc 1 24,.free 0,.free 1]) := by
  decide +kernel

theorem executable_larger_copy : observe 200 2 7 1 17 =
    some (17, materialize (finalState 2 7 1 17), [.alloc 0 24,.alloc 1 64,.free 0,.free 1]) := by
  decide +kernel

/-- Typing's no-live-owner conclusion applies unchanged to the generated
program's related final source heap. -/
theorem every_run_no_live
    (run : SizedCoreExecution.Eval graph (sourceEnv n m i value) 81
      SizedBufferHeap.empty result es t) : ∀ x, t.heap.live x = false :=
  SizedCompositionExamples.every_run_no_live run

end Jihoo.SizedMirBranchCoreExamples
