import Jihoo.SizedMirBranchCoreExamples
import Jihoo.NativeCompositionMirExecution

/-! Per-fixture correspondence for the unchanged root-81 source graph and its
retained native MIR. Structural source/MIR association is externally checked;
this is not a proof of arbitrary native lowering or signed arithmetic. -/
namespace Jihoo.NativeCompositionMirCorrespondence
open BoundedMir SizedMir

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def expectedHeap (n m i value : Nat) : Array Object :=
  if i < n then
    #[⟨false, MirBuffer.cells n value n⟩, ⟨false, MirBuffer.cells m value m⟩]
  else #[⟨false, MirBuffer.cells n value n⟩]

theorem heap_related (n m i value : Nat) :
    HeapRel (SizedMirBranchCoreExamples.finalState n m i value) (expectedHeap n m i value) := by
  unfold SizedMirBranchCoreExamples.finalState expectedHeap
  split <;> rename_i h
  · split <;> constructor
    all_goals
      first
      | rfl
      | intro j hj
        have bound : j < 2 := by simpa using hj
        have cases : j = 0 ∨ j = 1 := by omega
        rcases cases with rfl | rfl <;>
          simp [object, SizedCompositionExamples.finish,
            SizedCompositionExamples.copied, SizedCompositionExamples.allocated,
            SizedOwnedLend.final, SizedBufferHeap.release, SizedBufferHeap.restore,
            SizedBufferHeap.allocate, SizedBufferHeap.empty, HeapLeases.empty,
            HeapLeases.put, ScopedLend.restored]
  · constructor
    · rfl
    · intro j hj
      have same : j = 0 := by simp at hj; omega
      subst j
      simp [object, SizedCompositionExamples.allocated, SizedBufferHeap.release,
        SizedBufferHeap.allocate, SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put]

theorem lifecycle_eq (n m i value : Nat) :
    lifecycle (SizedMirBranchCoreExamples.events n m i value) =
      if i < n then [.alloc 0 (n*8+8), .alloc 1 (m*8+8), .free 0, .free 1]
      else [.alloc 0 (n*8+8), .free 0] := by
  unfold SizedMirBranchCoreExamples.events
  split
  · split <;> rfl
  · rfl

/-- Both programs implement the same original source execution, although their
local/block layouts differ. Existence of the native run is constructed. -/
theorem three_way_termination (capacity : n + m + 2 ≤ 4096)
    (index : i < wordBound) (payload : value < scalarBound) :
    entryFrame NativeCompositionMir.code NativeCompositionMir.entry
      [.u64 n, .u64 m, .u64 i, .i64 value] = some (NativeCompositionMir.inputs n m i value) ∧
    SizedCoreExecution.Eval SizedCompositionGraph.graph
      (SizedCompositionExamples.inputEnv n m i value) 81 SizedBufferHeap.empty
      (.scalar (if i < n then value else 99))
      (SizedMirBranchCoreExamples.events n m i value)
      (SizedMirBranchCoreExamples.finalState n m i value) ∧
    ∃ native generated,
      Steps NativeCompositionMir.code (.running (NativeCompositionMir.inputs n m i value))
        (lifecycle (SizedMirBranchCoreExamples.events n m i value))
        (.returned (if i < n then value else 99) native) ∧
      Steps SizedMirBranchCoreExamples.code
        (.running (Linear.start (Linear.programFrame SizedMirBranchCoreExamples.fragment
          (SizedMirBranchCoreExamples.frame n m i value))
          (Linear.entry 1 0 SizedMirBranchCoreExamples.term)))
        (lifecycle (SizedMirBranchCoreExamples.events n m i value))
        (.returned (if i < n then value else 99) generated) ∧
      HeapRel (SizedMirBranchCoreExamples.finalState n m i value) native.heap ∧
      native.heap = generated.heap ∧ heapEmpty native = true := by
  obtain ⟨first, second, native⟩ := NativeCompositionMir.terminates (i := i) capacity payload
  obtain ⟨generated, generatedRun, generatedHeap⟩ :=
    SizedMirBranchCoreExamples.generated_run (i := i) capacity payload
  have related : HeapRel (SizedMirBranchCoreExamples.finalState n m i value)
      (NativeCompositionMir.finalFrame n m i value first second).heap := by
    rw [NativeCompositionMir.final_heap]
    exact heap_related n m i value
  refine ⟨NativeCompositionMir.input_frame capacity index payload,
    SizedMirBranchCoreExamples.source_run n m i value, _, generated, ?_, generatedRun,
    related, related.unique generatedHeap, NativeCompositionMir.final_no_live⟩
  simpa only [lifecycle_eq, NativeCompositionMir.events] using native

/-- Any returned native execution agrees with any original source execution,
including the exact represented heap rather than only absence of leaks. -/
theorem every_execution_agrees (capacity : n + m + 2 ≤ 4096)
    (payload : value < scalarBound)
    (source : SizedCoreExecution.Eval SizedCompositionGraph.graph
      (SizedCompositionExamples.inputEnv n m i value) 81 SizedBufferHeap.empty
      sourceResult sourceEvents sourceFinal)
    (native : Steps NativeCompositionMir.code (.running (NativeCompositionMir.inputs n m i value))
      nativeEvents (.returned nativeResult nativeFinal)) :
    sourceResult = .scalar nativeResult ∧ lifecycle sourceEvents = nativeEvents ∧
      HeapRel sourceFinal nativeFinal.heap ∧ heapEmpty nativeFinal = true := by
  obtain ⟨sr, se, sf⟩ := source.deterministic (SizedMirBranchCoreExamples.source_run n m i value)
  obtain ⟨nr, ne, nh, empty⟩ := NativeCompositionMir.every_return capacity payload native
  refine ⟨?_, ?_, ?_, empty⟩
  · rw [sr, nr]
  · rw [se, ne, lifecycle_eq]; rfl
  · rw [sf, nh]
    exact heap_related n m i value

end Jihoo.NativeCompositionMirCorrespondence
