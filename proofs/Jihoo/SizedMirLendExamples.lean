import Jihoo.SizedMirLinearValueBounds
import Jihoo.SizedMirExamples

/-! Generated scalar and owned-result lenders. Lengths and indices remain runtime
inputs; source traces, rather than MIR validation, justify the reads. -/
namespace Jihoo.SizedMirLendExamples
open BoundedMir SizedMir SizedMir.Linear
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def prior := SizedMirExamples.prior
def initial (n value : Nat) := SizedBufferHeap.allocate prior n value
def scalarFinal (n value : Nat) := SizedBufferHeap.release (SizedBufferHeap.restore (initial n value)) 2
def ownedMiddle (n m value : Nat) := SizedOwnedLend.final (initial n value) m value
def ownedFinal (n m value : Nat) := SizedBufferHeap.release (SizedBufferHeap.release (ownedMiddle n m value) 2) 3

def types : Array Ty := #[.i64,.ptr,.u64,.u64,.u64,.i64]
def inputs : List Operand := [.copy ⟨1,false⟩,.copy ⟨2,false⟩,.copy ⟨3,false⟩,.copy ⟨4,false⟩,.copy ⟨5,false⟩]
def env (n m i value : Nat) : SizedErasure.Env := [.owner 2,.nat n,.nat m,.nat i,.scalar value]
def frame (n m i value : Nat) : Frame :=
  ⟨77,9,#[some (.i64 777),some (.pointer 2 0),some (.u64 n),some (.u64 m),some (.u64 i),some (.i64 value)],materialize (initial n value)⟩
def index : SizedErasure.NatTerm := .letE (.var 4) (.letE (.var 0) (.var 0))
def length : SizedErasure.NatTerm := .letE (.var 3) (.letE (.var 0) (.var 0))
def scalarTerm : SizedErasure.Term := .lend 0 index (.app (.var 1) (.app (.var 0) (.free 2 (.var 0))))
def ownedTerm : SizedErasure.Term := .ownedLend 0 length index
  (.app (.var 1) (.app (.var 0) (.free 2 (.free 0 (.var 8)))))
def scalarFragment := (compile inputs 6 1 0 scalarTerm).getD (pureFragment (.constant (.i64 0)))
def ownedFragment := (compile inputs 6 1 0 ownedTerm).getD (pureFragment (.constant (.i64 0)))
def scalarCode := program types scalarFragment
def ownedCode := program types ownedFragment

theorem scalar_compiled : lowerProgram types inputs scalarTerm = some scalarFragment := by decide +kernel
theorem owned_compiled : lowerProgram types inputs ownedTerm = some ownedFragment := by decide +kernel

def scalarEvents (i value : Nat) : List SizedBufferHeap.Event :=
  [.beginLease 0 2,.read 0 i value,.close 0,.free 2]
def ownedEvents (m i value : Nat) : List SizedBufferHeap.Event :=
  [.beginLease 0 2,.read 0 i value,.alloc 3 m value,.close 0,.free 2,.free 3]

theorem prior_valid : SizedBufferHeap.Valid prior := by
  apply SizedBufferHeap.step_valid
    (SizedBufferHeap.step_valid (SizedBufferHeap.step_valid SizedBufferHeap.empty_valid
      (SizedBufferHeap.Step.alloc (n := 1) (v := 73))) (SizedBufferHeap.Step.alloc (n := 0) (v := 5)))
  exact .free (by decide) (by intro token; simp [SizedBufferHeap.allocate, SizedBufferHeap.empty, HeapLeases.empty])
theorem initial_valid : SizedBufferHeap.Valid (initial n value) := SizedBufferHeap.step_valid prior_valid .alloc

theorem scalar_eval : SizedErasure.Eval (env n m i value) scalarTerm (initial n value)
    (.scalar value) (scalarEvents i value) (scalarFinal n value) := by
  apply SizedErasure.Eval.lend rfl (.letE (.var rfl) (.letE (.var rfl) (.var rfl)))
  apply SizedErasure.Eval.app (.var rfl)
  apply SizedErasure.Eval.app (.var rfl)
  exact .free rfl (.var rfl)

theorem owned_eval : SizedErasure.Eval (env n m i value) ownedTerm (initial n value)
    (.scalar value) (ownedEvents m i value) (ownedFinal n m value) := by
  apply SizedErasure.Eval.ownedLend rfl (.letE (.var rfl) (.letE (.var rfl) (.var rfl)))
    (.letE (.var rfl) (.letE (.var rfl) (.var rfl)))
  apply SizedErasure.Eval.app (.var rfl)
  apply SizedErasure.Eval.app (.var rfl)
  exact .free rfl (.free rfl (.var rfl))

private theorem original_live : (initial n value).heap.live 2 = true := by rfl
private theorem original_length : (initial n value).length 2 = n := by rfl

theorem scalar_safe (bound : i < n) :
    SizedBufferHeap.Steps (initial n value) (scalarEvents i value) (scalarFinal n value) := by
  have pre := SizedBufferHeap.read_cycle (initial_valid (n := n) (value := value)) original_live
    (show i < (initial n value).length 2 from bound)
  apply Trace.steps_append pre
  apply SizedBufferHeap.Steps.cons (.free (by rfl) ?_) .nil
  intro token
  simp [initial, prior, SizedMirExamples.prior, SizedBufferHeap.restore, ScopedLend.restored,
    SizedBufferHeap.allocate, SizedBufferHeap.release, SizedBufferHeap.empty, HeapLeases.empty]

theorem owned_safe (bound : i < n) :
    SizedBufferHeap.Steps (initial n value) (ownedEvents m i value) (ownedFinal n m value) := by
  have pre := SizedOwnedLend.prefix_steps (length := m) (initial_valid (n := n) (value := value)) original_live
    (show i < (initial n value).length 2 from bound)
  apply Trace.steps_append pre
  apply SizedBufferHeap.Steps.cons (.free (by rfl) ?_)
  · apply SizedBufferHeap.Steps.cons (.free (by rfl) ?_) .nil
    intro token
    simp [SizedOwnedLend.final, initial, prior, SizedMirExamples.prior, SizedBufferHeap.restore, ScopedLend.restored,
      SizedBufferHeap.allocate, SizedBufferHeap.release, SizedBufferHeap.empty, HeapLeases.empty]
  · intro token
    simp [SizedOwnedLend.final, initial, prior, SizedMirExamples.prior, SizedBufferHeap.restore, ScopedLend.restored,
      SizedBufferHeap.allocate, SizedBufferHeap.release, SizedBufferHeap.empty, HeapLeases.empty]

theorem scalar_bounds (capacity : n ≤ 4092) (payload : value < scalarBound) :
    Trace.Bounds (scalarFinal n value) := by
  constructor
  · change 3 ≤ 512; decide
  · change cellCount (SizedBufferHeap.release (SizedBufferHeap.restore (initial n value)) 2) ≤ 4096
    rw [cellCount_release]
    change cellCount (initial n value) ≤ 4096
    simp only [initial, cellCount_allocate]
    change 3 + n + 1 ≤ 4096
    omega
  · intro x old
    change x < 3 at old
    have cases' : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    rcases cases' with rfl | rfl | rfl <;>
      simp_all [scalarFinal, initial, prior, SizedMirExamples.prior, SizedBufferHeap.release,
        SizedBufferHeap.restore, ScopedLend.restored, SizedBufferHeap.allocate,
        SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put, scalarBound]

theorem owned_bounds (capacity : n + m ≤ 4091) (payload : value < scalarBound) :
    Trace.Bounds (ownedFinal n m value) := by
  constructor
  · change 4 ≤ 512; decide
  · simp only [ownedFinal, cellCount_release, ownedMiddle, SizedOwnedLend.final, cellCount_allocate]
    change cellCount (initial n value) + m + 1 ≤ 4096
    simp only [initial, cellCount_allocate]
    change 3 + n + 1 + m + 1 ≤ 4096
    omega
  · intro x old
    change x < 4 at old
    have cases' : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
    rcases cases' with rfl | rfl | rfl | rfl <;>
      simp_all [ownedFinal, ownedMiddle, SizedOwnedLend.final, initial, prior, SizedMirExamples.prior,
        SizedBufferHeap.release, SizedBufferHeap.restore, ScopedLend.restored, SizedBufferHeap.allocate,
        SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put, scalarBound]

theorem inputs_related : EnvRel (env n m i value) inputs (frame n m i value) :=
  .keep rfl (.keep rfl (.keep rfl (.keep rfl (.keep rfl .nil))))

theorem scalar_generated (bound : i < n) (capacity : n ≤ 4092) (payload : value < scalarBound) :
    ∃ final, Steps scalarCode
      (.running (start (programFrame scalarFragment (frame n m i value)) 1))
      [.free 2] (.returned value final) ∧ HeapRel (scalarFinal n value) final.heap := by
  obtain ⟨final, run, heap, _⟩ := program_run scalar_compiled (f := frame n m i value) rfl
    inputs_related (HeapRel.materialize_related _) initial_valid scalar_eval (scalar_safe bound) (scalar_bounds capacity payload)
  exact ⟨final, run, heap⟩

theorem owned_generated (bound : i < n) (capacity : n + m ≤ 4091) (payload : value < scalarBound) :
    ∃ final, Steps ownedCode
      (.running (start (programFrame ownedFragment (frame n m i value)) 1))
      [.alloc 3 (m*8+8),.free 2,.free 3] (.returned value final) ∧ HeapRel (ownedFinal n m value) final.heap := by
  obtain ⟨final, run, heap, _⟩ := program_run owned_compiled (f := frame n m i value) rfl
    inputs_related (HeapRel.materialize_related _) initial_valid owned_eval (owned_safe bound) (owned_bounds capacity payload)
  exact ⟨final, run, heap⟩

theorem inputs_bounded (hn : n < wordBound) (hm : m < wordBound) (hi : i < wordBound)
    (hv : value < scalarBound) : EnvBounded (env n m i value) := by
  simp [EnvBounded, env, ValueBounded, hn, hm, hi, hv]

theorem scalar_width (hn : n < wordBound) (hm : m < wordBound) (hi : i < wordBound)
    (hv : value < scalarBound) (bound : i < n) (capacity : n ≤ 4092) : ValueBounded (.scalar value) :=
  (lowerProgram_shape scalar_compiled).1.value_bounded (inputs_bounded hn hm hi hv)
    initial_valid scalar_eval (scalar_safe bound) (scalar_bounds capacity hv).payloads

theorem owned_width (hn : n < wordBound) (hm : m < wordBound) (hi : i < wordBound)
    (hv : value < scalarBound) (bound : i < n) (capacity : n + m ≤ 4091) : ValueBounded (.scalar value) :=
  (lowerProgram_shape owned_compiled).1.value_bounded (inputs_bounded hn hm hi hv)
    initial_valid owned_eval (owned_safe bound) (owned_bounds capacity hv).payloads

structure Observation where
  result : Nat
  heap : Array Object
  events : List Event
  deriving DecidableEq, Repr

def observe (fuel : Nat) (owned : Bool) (n m i value : Nat) : Option Observation := do
  let frag := if owned then ownedFragment else scalarFragment
  let out ← runFor fuel (program types frag) (.running (start (programFrame frag (frame n m i value)) 1))
  let .returned result final := out.machine | none
  return ⟨result, final.heap, out.events⟩

theorem scalar_executable_edge : observe 30 false 3 0 2 37 =
    some ⟨37,materialize (scalarFinal 3 37),[.free 2]⟩ := by decide +kernel

theorem owned_executable_zero : observe 40 true 1 0 0 37 =
    some ⟨37,materialize (ownedFinal 1 0 37),[.alloc 3 8,.free 2,.free 3]⟩ := by decide +kernel

theorem owned_executable_nonzero : observe 60 true 3 2 2 37 =
    some ⟨37,materialize (ownedFinal 3 2 37),[.alloc 3 24,.free 2,.free 3]⟩ := by decide +kernel

/-- The result allocation can be longer than the original; only the original
read index is constrained. -/
theorem owned_executable_longer_result : observe 80 true 1 4 0 37 =
    some ⟨37,materialize (ownedFinal 1 4 37),[.alloc 3 40,.free 2,.free 3]⟩ := by decide +kernel

theorem original_zero_rejected : observe 40 true 0 4 0 37 = none := by decide +kernel
theorem spare_cell_rejected : observe 40 false 3 0 3 37 = none := by decide +kernel
theorem outside_rejected : observe 40 true 3 1 4 37 = none := by decide +kernel

theorem scalar_no_safe_trace (outside : n ≤ i) :
    ¬ SizedBufferHeap.Steps (initial n value) (scalarEvents i value) t := by
  intro safe
  have bound := (Trace.lend_prefix initial_valid safe).2.1
  change i < n at bound
  omega

theorem owned_no_safe_trace (outside : n ≤ i) :
    ¬ SizedBufferHeap.Steps (initial n value) (ownedEvents m i value) t := by
  intro safe
  have bound := (Trace.owned_lend_prefix initial_valid safe).2.1
  change i < n at bound
  omega

theorem branch_rejected : lowerProgram types inputs
    (.ifLt (.literal 0) (.literal 1) scalarTerm ownedTerm) = none := by decide +kernel
theorem missing_owner_rejected : lowerProgram types inputs (.lend 5 index (.scalar 0)) = none := by decide +kernel
theorem malformed_index_rejected : lowerProgram types inputs (.lend 0 (.var 0) (.scalar 0)) = none := by decide +kernel
theorem malformed_length_rejected : lowerProgram types inputs (.ownedLend 0 (.var 0) index (.scalar 0)) = none := by decide +kernel
theorem dereference_operand_rejected : lowerProgram types
    [.copy ⟨1,true⟩,.copy ⟨2,false⟩,.copy ⟨3,false⟩,.copy ⟨4,false⟩,.copy ⟨5,false⟩] scalarTerm = none := by decide +kernel

/-- Static validation alone does not authorize a read after releasing its owner. -/
def afterFree : SizedErasure.Term := .free 0 scalarTerm
def afterFreeFragment := (compile inputs 6 1 0 afterFree).getD (pureFragment (.constant (.i64 0)))
theorem after_free_compiled : lowerProgram types inputs afterFree = some afterFreeFragment := by decide +kernel

theorem after_free_no_safe_trace :
    ¬ SizedBufferHeap.Steps (initial n value) (.free 2 :: scalarEvents i value) t := by
  intro run
  cases run with
  | cons free rest =>
    cases free with
    | free live unborrowed =>
      cases rest with
      | cons begin rest =>
        cases begin with
        | beginLease alive => simp [SizedBufferHeap.release, HeapLeases.put] at alive

theorem after_free_executable_rejected : runFor 30 (program types afterFreeFragment)
    (.running (start (programFrame afterFreeFragment (frame 3 0 1 37)) 1)) = none := by decide +kernel

/-! The unchanged original Core root 31 is opened under its true-branch proof
and owner/input environment. Compaction physically drops that proof binder;
this bridge makes no claim about a native exporter association. -/
open SizedBufferContext SizedCoreTyping

def sourceContext (n i : Nat) (bound : i < n) : Context :=
  .bound ⟨i,n,bound⟩ :: fresh (SizedCoreExamples.inputContext n i)
def sourceEnv (n i value : Nat) : SizedBufferContext.Env :=
  .ghost :: .owner 0 :: SizedCoreExamples.inputEnv n i value
def compactEnv (n i value : Nat) : SizedErasure.Env := [.owner 0,.scalar value,.nat i,.nat n]
def sourceTerm : SizedErasure.Term := .lend 0 (.var 3) (.free 0 (.var 1))
def sourceTypes : Array Ty := #[.i64,.ptr,.i64,.u64,.u64]
def sourceInputs : List Operand := [.copy ⟨1,false⟩,.copy ⟨2,false⟩,.copy ⟨3,false⟩,.copy ⟨4,false⟩]
def sourceFragment := (compile sourceInputs 5 1 0 sourceTerm).getD (pureFragment (.constant (.i64 0)))
def sourceFrame (n i value : Nat) : Frame :=
  ⟨77,9,#[some (.i64 777),some (.pointer 0 0),some (.i64 value),some (.u64 i),some (.u64 n)],
    materialize (SizedCoreExamples.allocated n value)⟩

theorem source_compacted : SizedErasure.compileTarget SizedCoreExamples.graph 128
    [false,true,true,true,true] 31 = some sourceTerm := by decide +kernel

theorem source_compiled : lowerProgram sourceTypes sourceInputs sourceTerm = some sourceFragment := by decide +kernel

theorem source_typed (bound : i < n) :
    Typing SizedCoreExamples.graph (sourceContext n i bound) [n] 31 .scalar := by
  apply Typing.lend (slot := 0) (n := n) (i := i) SizedCoreExamples.read_shape rfl rfl rfl
  · exact ⟨16,rfl,15,rfl,DependentBufferIndices.Eval.var rfl rfl⟩
  · exact ⟨24,rfl,DependentBufferIndices.Eval.var rfl rfl⟩
  · exact DependentBufferIndices.Eval.var rfl rfl
  · exact .var (fact := ⟨i,n,bound⟩) rfl rfl
  · exact .free (slot := 0) rfl rfl rfl (by simp) (.scalar rfl rfl)

theorem source_agrees (bound : i < n) : Agrees (sourceContext n i bound) [0] (sourceEnv n i value) :=
  (SizedCoreExamples.input_agrees n i value).fresh.bound

theorem source_layout : Layout (SizedCoreExamples.allocated n value) [0] [n] :=
  SizedCoreExamples.empty_layout.allocate SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns

theorem source_owned : LinearHeapPrograms.Owns (SizedCoreExamples.allocated n value).heap [0] :=
  LinearHeapPrograms.allocate_owns SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns

theorem source_initial_valid : SizedBufferHeap.Valid (SizedCoreExamples.allocated n value) :=
  SizedBufferHeap.step_valid SizedBufferHeap.empty_valid .alloc

theorem source_run : SizedCoreExecution.Eval SizedCoreExamples.graph (sourceEnv n i value) 31
    (SizedCoreExamples.allocated n value) (.scalar value)
    [.beginLease 0 0,.read 0 i value,.close 0,.free 0] (SizedCoreExamples.readFinal n value) :=
  .lend SizedCoreExamples.read_shape rfl rfl (DependentBufferIndices.Eval.var rfl rfl)
    (.free rfl rfl rfl (.var rfl rfl))

theorem source_erased : SizedErasure.EnvRel [false,true,true,true,true] (sourceEnv n i value) (compactEnv n i value) :=
  .consGhost (.consKeep (.owner 0) (.consKeep (.scalar value) (.consKeep (.nat i) (.consKeep (.nat n) .nil))))

theorem source_related : EnvRel (compactEnv n i value) sourceInputs (sourceFrame n i value) :=
  .keep rfl (.keep rfl (.keep rfl (.keep rfl .nil)))

theorem source_bounds (capacity : n ≤ 4095) (payload : value < scalarBound) :
    Trace.Bounds (SizedCoreExamples.readFinal n value) := by
  constructor
  · change 1 ≤ 512; decide
  · simp only [SizedCoreExamples.readFinal, cellCount_release]
    change cellCount (SizedCoreExamples.allocated n value) ≤ 4096
    simp only [SizedCoreExamples.allocated, cellCount_allocate]
    change 0 + n + 1 ≤ 4096
    omega
  · intro x old
    change x < 1 at old
    have eq : x = 0 := by omega
    subst x
    exact payload

/-- The real typing derivation, erased proof/environment correspondence and
source execution supply read/release safety to the generated program theorem. -/
theorem original_core_to_generated (bound : i < n) (capacity : n ≤ 4095) (payload : value < scalarBound) :
    ∃ final, Steps (program sourceTypes sourceFragment)
      (.running (start (programFrame sourceFragment (sourceFrame n i value)) 1))
      [.free 0] (.returned value final) ∧ HeapRel (SizedCoreExamples.readFinal n value) final.heap := by
  obtain ⟨final, run, heap, _⟩ := typed_source_run source_compacted source_compiled
    (source_typed bound) source_erased (source_agrees bound) source_layout source_initial_valid source_owned
    (f := sourceFrame n i value) rfl source_related (HeapRel.materialize_related _) source_run
    (source_bounds capacity payload)
  exact ⟨final, run, heap⟩

/-- Source totality is discharged against the explicit execution, so no target
termination premise or arbitrary source/MIR association enters this result. -/
theorem original_core_total (bound : i < n) (capacity : n ≤ 4095) (payload : value < scalarBound) :
    ∃ result events t final,
      SizedCoreExecution.Eval SizedCoreExamples.graph (sourceEnv n i value) 31
        (SizedCoreExamples.allocated n value) (.scalar result) events t ∧
      Steps (program sourceTypes sourceFragment)
        (.running (start (programFrame sourceFragment (sourceFrame n i value)) 1))
        (lifecycle events) (.returned result final) ∧ HeapRel t final.heap ∧
      Account [0] (.scalar result) events := by
  apply typed_source_total source_compacted source_compiled (source_typed bound) source_erased
    (source_agrees bound) source_layout source_initial_valid source_owned rfl source_related
    (HeapRel.materialize_related _)
  intro result events t run
  obtain ⟨_,_,same⟩ := run.deterministic source_run
  rw [same]
  exact source_bounds capacity payload

/-- Explicit machine-width assumptions accompany source trace and heap bounds.
The environment relation alone does not establish these bounds. -/
theorem owned_bounded_generated (hn : n < wordBound) (hm : m < wordBound) (hi : i < wordBound)
    (hv : value < scalarBound) (bound : i < n) (capacity : n + m ≤ 4091) :
    value < scalarBound ∧ ∃ final, Steps ownedCode
      (.running (start (programFrame ownedFragment (frame n m i value)) 1))
      [.alloc 3 (m*8+8),.free 2,.free 3] (.returned value final) ∧
      HeapRel (ownedFinal n m value) final.heap := by
  obtain ⟨width, final, run, heap, _⟩ := bounded_program_run owned_compiled
    (f := frame n m i value) rfl inputs_related (HeapRel.materialize_related _) initial_valid
    owned_eval (owned_safe bound) (owned_bounds capacity hv) (inputs_bounded hn hm hi hv)
  exact ⟨width,final,run,heap⟩

end Jihoo.SizedMirLendExamples
