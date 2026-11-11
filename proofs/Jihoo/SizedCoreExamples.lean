import Jihoo.SizedCoreSafety
import Jihoo.SizedCoreDeterminism
import Jihoo.DependentBufferGraph

/-! One unchanged checked source graph is interpreted at arbitrary closing n/i.
The body is opened under its explicit runtime U64/U64/I64 parameters. This is
not a proof of native ABI entry or a general dependent Pi theorem. -/
namespace Jihoo.SizedCoreExamples
open ScopedLend SizedBufferContext SizedCoreExecution SizedCoreTyping
open DependentBufferIndices

abbrev graph := DependentBufferGraph.graph

def inputContext (n i : Nat) : Context := [.scalar, .nat i, .nat n]

theorem read_shape : ReadLend graph 31 14 17 19 20 25 28 :=
  .intro rfl rfl rfl rfl rfl rfl rfl

/-- The same source graph, not a length-specialized graph, has a closing typing
for every length/index. The false branch performs no read, including n=0. -/
theorem body_typed (n i : Nat) : Typing graph (inputContext n i) [] 40 .scalar := by
  apply Typing.allocate (function := 36) (argument := 39) (domain := 11)
    (length := 37) (init := 38) (n := n) rfl rfl
  · exact ⟨10, rfl, Eval.var rfl rfl⟩
  · rfl
  · exact Eval.var rfl rfl
  · exact .var rfl rfl
  · apply Typing.branch (left := 12) (right := 13) (a := i) (b := n) rfl
    · exact Eval.var rfl rfl
    · exact Eval.var rfl rfl
    · intro bound
      apply Typing.lend (slot := 0) (n := n) (i := i) read_shape rfl rfl rfl
      · exact ⟨16, rfl, 15, rfl, Eval.var rfl rfl⟩
      · exact ⟨24, rfl, Eval.var rfl rfl⟩
      · exact Eval.var rfl rfl
      · exact .var (fact := ⟨i,n,bound⟩) rfl rfl
      · exact .free (slot := 0) rfl rfl rfl (by simp) (.scalar rfl rfl)
    · intro outside
      exact .free (slot := 0) rfl rfl rfl (by simp)
        (.literal rfl (by decide))

/-- The allocation subexpression preserves its dependent result length. -/
theorem allocation_typed (n i : Nat) :
    Typing graph (inputContext n i) [] 39 (.owner n) :=
  .allocation rfl (Eval.var rfl rfl) (.var rfl rfl)

def inputEnv (n i value : Nat) : SizedBufferContext.Env :=
  [.scalar value, .nat i, .nat n]

theorem valid_inputs (hn : n < 2^64) (hi : i < 2^64) : ValidNats (inputContext n i) := by
  intro k v lookup
  cases k with
  | zero => simp [naturalEnv, inputContext] at lookup
  | succ k =>
    cases k with
    | zero => simp [naturalEnv, inputContext] at lookup; subst v; exact hi
    | succ k =>
      cases k with
      | zero => simp [naturalEnv, inputContext] at lookup; subst v; exact hn
      | succ k => simp [naturalEnv, inputContext] at lookup

theorem input_agrees (n i value : Nat) : Agrees (inputContext n i) [] (inputEnv n i value) := by
  constructor
  · intro k v lookup
    cases k with
    | zero => simp [inputContext] at lookup
    | succ k =>
      cases k with
      | zero => simp [inputContext] at lookup; subst v; rfl
      | succ k =>
        cases k with
        | zero => simp [inputContext] at lookup; subst v; rfl
        | succ k => simp [inputContext] at lookup
  · intro k lookup
    cases k with
    | zero => exact ⟨value, rfl⟩
    | succ k =>
      cases k with
      | zero => simp [inputContext] at lookup
      | succ k => cases k <;> simp [inputContext] at lookup
  · intro k slot lookup
    cases k with
    | zero => simp [inputContext] at lookup
    | succ k =>
      cases k with
      | zero => simp [inputContext] at lookup
      | succ k => cases k <;> simp [inputContext] at lookup
  · intro k fact lookup
    cases k with
    | zero => simp [inputContext] at lookup
    | succ k =>
      cases k with
      | zero => simp [inputContext] at lookup
      | succ k => cases k <;> simp [inputContext] at lookup

def allocated (n value : Nat) : SizedBufferHeap.State :=
  SizedBufferHeap.allocate SizedBufferHeap.empty n value

def noReadFinal (n value : Nat) : SizedBufferHeap.State :=
  SizedBufferHeap.release (allocated n value) 0

def readFinal (n value : Nat) : SizedBufferHeap.State :=
  SizedBufferHeap.release
    ⟨ScopedLend.restored (allocated n value).heap, (allocated n value).length⟩ 0

def readEvents (n i value : Nat) : List SizedBufferHeap.Event :=
  [.alloc 0 n value, .beginLease 0 0, .read 0 i value, .close 0, .free 0]

theorem allocation_run (n i value : Nat) :
    SizedCoreExecution.Eval graph (inputEnv n i value) 39 SizedBufferHeap.empty
      (.owner 0) [.alloc 0 n value] (allocated n value) :=
  .allocate rfl (Eval.var rfl rfl) (.var rfl rfl)

theorem body_read_run (bound : i < n) :
    SizedCoreExecution.Eval graph (inputEnv n i value) 40 SizedBufferHeap.empty
      (.scalar value) (readEvents n i value) (readFinal n value) := by
  apply SizedCoreExecution.Eval.app rfl rfl (allocation_run n i value)
  apply SizedCoreExecution.Eval.yes rfl (Eval.var rfl rfl) (Eval.var rfl rfl) bound
  exact .lend read_shape rfl rfl (Eval.var rfl rfl)
    (.free rfl rfl rfl (.var rfl rfl))

theorem body_no_read_run (outside : ¬ i < n) :
    SizedCoreExecution.Eval graph (inputEnv n i value) 40 SizedBufferHeap.empty
      (.scalar 99) [.alloc 0 n value, .free 0] (noReadFinal n value) := by
  apply SizedCoreExecution.Eval.app rfl rfl (allocation_run n i value)
  apply SizedCoreExecution.Eval.no rfl (Eval.var rfl rfl) (Eval.var rfl rfl) outside
  exact .free rfl rfl rfl (.scalar rfl)

theorem zero_length_run (i value : Nat) :
    SizedCoreExecution.Eval graph (inputEnv 0 i value) 40 SizedBufferHeap.empty
      (.scalar 99) [.alloc 0 0 value, .free 0] (noReadFinal 0 value) :=
  body_no_read_run (by omega)

def bodyEvents (n i value : Nat) : List SizedBufferHeap.Event :=
  if i < n then readEvents n i value else [.alloc 0 n value, .free 0]

def bodyFinal (n i value : Nat) : SizedBufferHeap.State :=
  if i < n then readFinal n value else noReadFinal n value

theorem body_run (n i value : Nat) :
    SizedCoreExecution.Eval graph (inputEnv n i value) 40 SizedBufferHeap.empty
      (.scalar (if i < n then value else 99)) (bodyEvents n i value) (bodyFinal n i value) := by
  by_cases h : i < n
  · simpa [bodyEvents, bodyFinal, h] using body_read_run (value := value) h
  · simpa [bodyEvents, bodyFinal, h] using body_no_read_run (value := value) h

theorem every_run_exact
    (run : SizedCoreExecution.Eval graph (inputEnv n i value) 40 SizedBufferHeap.empty result events t) :
    result = .scalar (if i < n then value else 99) ∧
      events = bodyEvents n i value ∧ t = bodyFinal n i value :=
  run.deterministic (body_run n i value)

theorem body_final_no_live (n i value x : Nat) : (bodyFinal n i value).heap.live x = false := by
  by_cases choice : i < n <;> by_cases same : x = 0 <;>
    simp [bodyFinal, readFinal, noReadFinal, allocated, SizedBufferHeap.release,
      SizedBufferHeap.allocate, SizedBufferHeap.empty, ScopedLend.restored,
      HeapLeases.empty, HeapLeases.put, choice, same]

theorem every_run_releases_all
    (run : SizedCoreExecution.Eval graph (inputEnv n i value) 40 SizedBufferHeap.empty result events t) :
    ∀ x, t.heap.live x = false := by
  rw [(every_run_exact run).2.2]
  exact body_final_no_live n i value

theorem empty_layout : Layout SizedBufferHeap.empty [] [] := by
  constructor
  · rfl
  · intro k x n lookup size; simp at lookup

theorem every_u64_run_safe (hn : n < 2^64) (hi : i < 2^64)
    (run : SizedCoreExecution.Eval graph (inputEnv n i value) 40 SizedBufferHeap.empty result events t) :
    ValidNats (inputContext n i) ∧ SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧
      SizedBufferHeap.Valid t ∧ Post .scalar t result := by
  exact ⟨valid_inputs hn hi, (body_typed n i).every_run_safe (input_agrees n i value)
    empty_layout HeapLeases.empty_valid LinearHeapPrograms.empty_owns run⟩

theorem allocated_result_length
    (run : SizedCoreExecution.Eval graph (inputEnv n i value) 39 SizedBufferHeap.empty result events t) :
    result = .owner 0 ∧ t.length 0 = n := by
  obtain ⟨rfl, _, rfl⟩ := run.deterministic (allocation_run n i value)
  exact ⟨rfl, by simp [allocated, SizedBufferHeap.allocate, SizedBufferHeap.empty, HeapLeases.empty, HeapLeases.put]⟩

end Jihoo.SizedCoreExamples
