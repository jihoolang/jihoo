import Jihoo.SizedMirLinearProgram
import Jihoo.SizedCompositionExamples

/-! Derived Core owned-result reader with a straight-line continuation. Node 61
is replaced by the existing no-read continuation at node 60. This is not a
claim that the native exporter produced this modified graph. -/
namespace Jihoo.SizedMirOwnedCoreExamples
open ScopedLend SizedBufferContext SizedCoreTyping SizedCoreExecution DependentBufferIndices
open BoundedMir SizedMir SizedMir.Linear
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def graph : Graph.Graph := SizedCompositionGraph.graph.set! 61 (.free 56 59)
def ctx (n m i : Nat) (bound : i < n) : Context :=
  [.bound ⟨i,n,bound⟩,.owner 0,.scalar,.nat i,.nat m,.nat n]
def sourceEnv (n m i value : Nat) : SizedBufferContext.Env :=
  [.ghost,.owner 0,.scalar value,.nat i,.nat m,.nat n]
def env (n m i value : Nat) : SizedErasure.Env :=
  [.owner 0,.scalar value,.nat i,.nat m,.nat n]
def mask : SizedErasure.Mask := [false,true,true,true,true,true]
def term : SizedErasure.Term :=
  .ownedLend 0 (.var 4) (.var 3)
    (.app (.app (.var 1) (.var 0)) (.free 1 (.free 0 (.var 4))))

theorem copy_shape : OwnedReadLend graph 72 17 20 21 23 24 29 31 69 :=
  .intro rfl rfl rfl rfl rfl rfl rfl

theorem typed (bound : i < n) : Typing graph (ctx n m i bound) [n] 72 .scalar := by
  apply Typing.ownedLend (slot := 0) (n := n) (m := m) (i := i) copy_shape rfl rfl rfl
  · exact ⟨19, rfl, 18, rfl, Eval.var rfl rfl⟩
  · exact Eval.var rfl rfl
  · exact ⟨28, rfl, Eval.var rfl rfl⟩
  · exact ⟨30, rfl, Eval.var rfl rfl⟩
  · exact Eval.var rfl rfl
  · exact .var (fact := ⟨i,n,bound⟩) rfl rfl
  · apply Typing.framedApp (function := 62) (argument := 68) (domain := 33)
      (p := 1) (n := m) rfl rfl (by simp)
    · exact ⟨32, rfl, Eval.var rfl rfl⟩
    · apply Typing.ownedLet (function := 66) (argument := 67) (domain := 64)
        (slot := 0) (n := m) rfl rfl rfl rfl rfl
      · exact ⟨63, rfl, Eval.var rfl rfl⟩
      · exact .owner rfl rfl
    · apply Typing.free (slot := 1) rfl rfl rfl (by simp)
      exact .free (slot := 0) rfl rfl rfl (by simp) (.scalar rfl rfl)

theorem compacted : SizedErasure.compileTarget graph 128 mask 72 = some term := by decide +kernel

def initial := SizedCompositionExamples.allocated
def finalState (n m value : Nat) := SizedCompositionExamples.finish (SizedCompositionExamples.copied n m value)
def events (m i value : Nat) : List SizedBufferHeap.Event :=
  [.beginLease 0 0,.read 0 i value,.alloc 1 m value,.close 0,.free 0,.free 1]

theorem source_run : SizedCoreExecution.Eval graph (sourceEnv n m i value) 72
    (initial n value) (.scalar value) (events m i value) (finalState n m value) := by
  apply SizedCoreExecution.Eval.ownedLend copy_shape rfl rfl
    (Eval.var rfl rfl) (Eval.var rfl rfl)
  apply SizedCoreExecution.Eval.app rfl rfl
    (.app rfl rfl (.var rfl rfl) (.var rfl rfl))
  exact .free rfl rfl rfl (.free rfl rfl rfl (.var rfl rfl))

theorem agrees (bound : i < n) : Agrees (ctx n m i bound) [0] (sourceEnv n m i value) := by
  exact (SizedCompositionExamples.input_agrees n m i value).fresh.bound

theorem initial_valid : SizedBufferHeap.Valid (initial n value) :=
  SizedBufferHeap.step_valid SizedBufferHeap.empty_valid .alloc

theorem initial_owned : LinearHeapPrograms.Owns (initial n value).heap [0] := by
  constructor
  · simp
  · intro x member; simp only [List.mem_singleton] at member; subst x; rfl
  · intro x member token
    simp [initial, SizedCompositionExamples.allocated, SizedBufferHeap.allocate,
      SizedBufferHeap.empty, HeapLeases.empty]

theorem initial_layout : Layout (initial n value) [0] [n] := by
  apply Layout.allocate (s := SizedBufferHeap.empty) (owners := []) (sizes := [])
    ⟨rfl, by simp⟩ SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns

theorem erased : SizedErasure.EnvRel mask (sourceEnv n m i value) (env n m i value) :=
  .consGhost (.consKeep (.owner 0) (.consKeep (.scalar value)
    (.consKeep (.nat i) (.consKeep (.nat m) (.consKeep (.nat n) .nil)))))

def inputTypes : Array Ty := #[.i64,.ptr,.i64,.u64,.u64,.u64]
def inputs : List Operand := [.copy ⟨1,false⟩,.copy ⟨2,false⟩,.copy ⟨3,false⟩,
  .copy ⟨4,false⟩,.copy ⟨5,false⟩]
def fragment : Fragment := (compile inputs ((inputKinds inputTypes inputs).getD []) 6 1 0 term).getD (pureFragment (.constant (.i64 0)))
def code : Code := program inputTypes fragment

theorem lowered : lowerProgram inputTypes inputs term = some fragment := by decide +kernel

def frame (n m i value : Nat) : Frame :=
  ⟨0,0,#[some (.i64 777),some (.pointer 0 0),some (.i64 value),some (.u64 i),
    some (.u64 m),some (.u64 n)],materialize (initial n value)⟩

theorem related : EnvRel (env n m i value) inputs (frame n m i value) :=
  .keep rfl (.keep rfl (.keep rfl (.keep rfl (.keep rfl .nil))))

theorem final_bounds (capacity : n + m + 2 ≤ 4096) (payload : value < scalarBound) :
    Trace.Bounds (finalState n m value) := by
  constructor
  · change 2 ≤ 512; decide
  · simp only [finalState, SizedCompositionExamples.finish, cellCount_release,
      SizedCompositionExamples.copied, SizedOwnedLend.final, cellCount_allocate]
    change cellCount (SizedCompositionExamples.allocated n value) + m + 1 ≤ 4096
    rw [SizedCompositionExamples.allocated, cellCount_allocate]
    have empty : cellCount SizedBufferHeap.empty = 0 := rfl
    rw [empty]
    omega
  · intro objectId old
    change objectId < 2 at old
    have alternatives : objectId = 0 ∨ objectId = 1 := by omega
    rcases alternatives with rfl | rfl <;>
      simpa [finalState, SizedCompositionExamples.finish, SizedCompositionExamples.copied,
        SizedCompositionExamples.allocated, SizedOwnedLend.final, SizedBufferHeap.release,
        SizedBufferHeap.allocate, SizedBufferHeap.restore, restored,
        SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put] using payload

/-- Actual Core typing supplies release safety; the target program is computed
from the compacted graph, not supplied as a matching pair. -/
theorem generated_run (bound : i < n) (capacity : n + m + 2 ≤ 4096)
    (payload : value < scalarBound) :
    ∃ final, Steps code
      (.running (start (programFrame fragment (frame n m i value)) (entry 1 0 term)))
      (lifecycle (events m i value)) (.returned value final) ∧
      HeapRel (finalState n m value) final.heap := by
  obtain ⟨final, target, heap, _⟩ := typed_source_run compacted lowered (typed bound)
    erased (agrees bound) initial_layout initial_valid initial_owned
    (f := frame n m i value) rfl related rfl (HeapRel.materialize_related _)
    source_run (final_bounds capacity payload)
  exact ⟨final,target,heap⟩

/-- Resource adequacy for every source execution follows by determinism, and
therefore typing alone constructs both source and generated target executions. -/
theorem typed_total (bound : i < n) (capacity : n + m + 2 ≤ 4096)
    (payload : value < scalarBound) :
    ∃ result es t final,
      SizedCoreExecution.Eval graph (sourceEnv n m i value) 72 (initial n value)
        (.scalar result) es t ∧
      Steps code (.running (start (programFrame fragment (frame n m i value)) (entry 1 0 term)))
        (lifecycle es) (.returned result final) ∧ HeapRel t final.heap ∧
      Account [0] (.scalar result) es := by
  apply typed_source_total compacted lowered (typed bound) erased (agrees bound)
    initial_layout initial_valid initial_owned rfl related rfl (HeapRel.materialize_related _)
  intro result es t run
  obtain ⟨_,_,same⟩ := run.deterministic source_run
  rw [same]
  exact final_bounds capacity payload

theorem generated_valid : valid code = true := lowerProgram_valid lowered

/-- A zero-length copy still performs a valid read of the original buffer,
allocates its spare cell, and releases both distinct owners. -/
def observe (fuel n m i value : Nat) : Option (Nat × Array Object × List BoundedMir.Event) := do
  let out ← runFor fuel code
    (.running (start (programFrame fragment (frame n m i value)) (entry 1 0 term)))
  let .returned result final := out.machine | none
  return (result, final.heap, out.events)

theorem executable_zero : observe 100 7 0 6 42 =
    some (42, materialize (finalState 7 0 42), [.alloc 1 8,.free 0,.free 1]) := by
  decide +kernel

theorem executable_distinct_lengths : observe 100 7 2 6 42 =
    some (42, materialize (finalState 7 2 42), [.alloc 1 24,.free 0,.free 1]) := by
  decide +kernel

theorem every_run_value
    (run : SizedCoreExecution.Eval graph (sourceEnv n m i value) 72
      (initial n value) result es t) : result = .scalar value :=
  (run.deterministic source_run).1

theorem final_no_live (x : Nat) : (finalState n m value).heap.live x = false := by
  simp [finalState, SizedCompositionExamples.finish, SizedCompositionExamples.copied,
    SizedCompositionExamples.allocated, SizedOwnedLend.final, SizedBufferHeap.release,
    SizedBufferHeap.allocate, SizedBufferHeap.restore, restored,
    SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put]
  exact fun h1 h0 => ⟨h1,h0⟩

end Jihoo.SizedMirOwnedCoreExamples
