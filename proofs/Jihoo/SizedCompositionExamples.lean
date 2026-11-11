import Jihoo.SizedCoreAccounting
import Jihoo.SizedCompositionGraph

/-! One native-exported graph with independently closing n/m lengths. The body
is opened under its four explicit parameters; ABI association remains trusted.
The typing derivation uses framed application and an owned-result lease. -/
namespace Jihoo.SizedCompositionExamples
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open ScopedLend SizedBufferContext SizedCoreExecution SizedCoreTyping
open DependentBufferIndices

abbrev graph := SizedCompositionGraph.graph

def inputContext (n m i : Nat) : Context := [.scalar, .nat i, .nat m, .nat n]
def inputEnv (n m i value : Nat) : SizedBufferContext.Env :=
  [.scalar value, .nat i, .nat m, .nat n]

theorem copy_shape : OwnedReadLend graph 72 17 20 21 23 24 29 31 69 :=
  .intro rfl rfl rfl rfl rfl rfl rfl

theorem observe_shape : ReadLend graph 55 36 39 41 42 47 52 :=
  .intro rfl rfl rfl rfl rfl rfl rfl

/-- Arbitrary independent closing lengths, including a zero-length owned
reader result, share the exact same graph and node IDs. -/
theorem body_typed (n m i : Nat) : Typing graph (inputContext n m i) [] 81 .scalar := by
  apply Typing.allocate (function := 77) (argument := 80) (domain := 14)
    (length := 78) (init := 79) (n := n) rfl rfl
  · exact ⟨13, rfl, Eval.var rfl rfl⟩
  · rfl
  · exact Eval.var rfl rfl
  · exact .var rfl rfl
  · apply Typing.branch (left := 15) (right := 16) (a := i) (b := n) rfl
    · exact Eval.var rfl rfl
    · exact Eval.var rfl rfl
    · intro bound
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
        · apply Typing.branch (left := 34) (right := 35) (a := 0) (b := m) rfl
          · exact Eval.literal rfl (by decide)
          · exact Eval.var rfl rfl
          · intro nonzero
            apply Typing.lend (slot := 0) (n := m) (i := 0) observe_shape rfl rfl rfl
            · exact ⟨38, rfl, 37, rfl, Eval.var rfl rfl⟩
            · exact ⟨46, rfl, Eval.var rfl rfl⟩
            · exact Eval.literal rfl (by decide)
            · exact .var (fact := ⟨0,m,nonzero⟩) rfl rfl
            · apply Typing.free (slot := 1) rfl rfl rfl (by simp)
              exact .free (slot := 0) rfl rfl rfl (by simp) (.scalar rfl rfl)
          · intro zero
            apply Typing.free (slot := 1) rfl rfl rfl (by simp)
            exact .free (slot := 0) rfl rfl rfl (by simp) (.scalar rfl rfl)
    · intro outside
      exact .free (slot := 0) rfl rfl rfl (by simp) (.literal rfl (by decide))

/-- Non-equal input and output lengths are admitted, not collapsed to Buffer1. -/
theorem distinct_lengths_typed : Typing graph (inputContext 7 2 6) [] 81 .scalar :=
  body_typed 7 2 6

theorem zero_result_length_typed : Typing graph (inputContext 7 0 6) [] 81 .scalar :=
  body_typed 7 0 6

theorem input_agrees (n m i value : Nat) :
    Agrees (inputContext n m i) [] (inputEnv n m i value) := by
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
        | succ k =>
          cases k with
          | zero => simp [inputContext] at lookup; subst v; rfl
          | succ k => simp [inputContext] at lookup
  · intro k lookup
    cases k with
    | zero => exact ⟨value,rfl⟩
    | succ k => cases k with
      | zero => simp [inputContext] at lookup
      | succ k => cases k with
        | zero => simp [inputContext] at lookup
        | succ k => cases k <;> simp [inputContext] at lookup
  · intro k slot lookup
    cases k with
    | zero => simp [inputContext] at lookup
    | succ k => cases k with
      | zero => simp [inputContext] at lookup
      | succ k => cases k with
        | zero => simp [inputContext] at lookup
        | succ k => cases k <;> simp [inputContext] at lookup
  · intro k fact lookup
    cases k with
    | zero => simp [inputContext] at lookup
    | succ k => cases k with
      | zero => simp [inputContext] at lookup
      | succ k => cases k with
        | zero => simp [inputContext] at lookup
        | succ k => cases k <;> simp [inputContext] at lookup

theorem every_run_no_live
    (run : SizedCoreExecution.Eval graph (inputEnv n m i value) 81
      SizedBufferHeap.empty result events t) : ∀ x, t.heap.live x = false :=
  (body_typed n m i).closed_scalar_empty (input_agrees n m i value) run

theorem body_total (n m i value : Nat) :
    ∃ result events t, SizedCoreExecution.Eval graph (inputEnv n m i value) 81
      SizedBufferHeap.empty result events t ∧ SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧
      SizedBufferHeap.Valid t ∧ Post .scalar t result ∧ Account [] result events :=
  (body_typed n m i).total_accounted (input_agrees n m i value) ⟨rfl, by simp⟩
    SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns

def allocated (n value : Nat) : SizedBufferHeap.State :=
  SizedBufferHeap.allocate SizedBufferHeap.empty n value

def copied (n m value : Nat) : SizedBufferHeap.State :=
  SizedOwnedLend.final (allocated n value) m value

def finish (s : SizedBufferHeap.State) : SizedBufferHeap.State :=
  SizedBufferHeap.release (SizedBufferHeap.release s 0) 1

/-- Concrete source execution returns the copied payload, not merely a live
owner. Zero-sized results use the source's no-read branch. -/
theorem body_value_run (n m i value : Nat) :
    ∃ events t, SizedCoreExecution.Eval graph (inputEnv n m i value) 81
      SizedBufferHeap.empty (.scalar (if i < n then value else 99)) events t := by
  by_cases readable : i < n
  · simp only [ite_eq_left readable]
    by_cases nonzero : 0 < m
    · refine ⟨[.alloc 0 n value, .beginLease 0 0, .read 0 i value,
        .alloc 1 m value, .close 0, .beginLease 1 1, .read 1 0 value,
        .close 1, .free 0, .free 1], finish (SizedBufferHeap.restore (copied n m value)), ?_⟩
      apply SizedCoreExecution.Eval.app rfl rfl
        (.allocate rfl (Eval.var rfl rfl) (.var rfl rfl))
      apply SizedCoreExecution.Eval.yes rfl (Eval.var rfl rfl) (Eval.var rfl rfl) readable
      apply SizedCoreExecution.Eval.ownedLend copy_shape rfl rfl
        (Eval.var rfl rfl) (Eval.var rfl rfl)
      apply SizedCoreExecution.Eval.app rfl rfl
        (.app rfl rfl (.var rfl rfl) (.var rfl rfl))
      apply SizedCoreExecution.Eval.yes rfl (Eval.literal rfl (by decide))
        (Eval.var rfl rfl) nonzero
      exact .lend observe_shape rfl rfl (Eval.literal rfl (by decide))
        (.free rfl rfl rfl (.free rfl rfl rfl (.var rfl rfl)))
    · refine ⟨[.alloc 0 n value, .beginLease 0 0, .read 0 i value,
        .alloc 1 m value, .close 0, .free 0, .free 1], finish (copied n m value), ?_⟩
      apply SizedCoreExecution.Eval.app rfl rfl
        (.allocate rfl (Eval.var rfl rfl) (.var rfl rfl))
      apply SizedCoreExecution.Eval.yes rfl (Eval.var rfl rfl) (Eval.var rfl rfl) readable
      apply SizedCoreExecution.Eval.ownedLend copy_shape rfl rfl
        (Eval.var rfl rfl) (Eval.var rfl rfl)
      apply SizedCoreExecution.Eval.app rfl rfl
        (.app rfl rfl (.var rfl rfl) (.var rfl rfl))
      apply SizedCoreExecution.Eval.no rfl (Eval.literal rfl (by decide))
        (Eval.var rfl rfl) nonzero
      exact .free rfl rfl rfl (.free rfl rfl rfl (.var rfl rfl))
  · simp only [ite_eq_right readable]
    refine ⟨[.alloc 0 n value, .free 0], SizedBufferHeap.release (allocated n value) 0, ?_⟩
    apply SizedCoreExecution.Eval.app rfl rfl
      (.allocate rfl (Eval.var rfl rfl) (.var rfl rfl))
    apply SizedCoreExecution.Eval.no rfl (Eval.var rfl rfl) (Eval.var rfl rfl) readable
    exact .free rfl rfl rfl (.scalar rfl)

theorem every_run_value
    (run : SizedCoreExecution.Eval graph (inputEnv n m i value) 81
      SizedBufferHeap.empty result events t) :
    result = .scalar (if i < n then value else 99) := by
  obtain ⟨_, _, canonical⟩ := body_value_run n m i value
  exact (run.deterministic canonical).1

end Jihoo.SizedCompositionExamples
