import Jihoo.LinearHeapPrograms
import Jihoo.ScopedLendGraphExamples

namespace Jihoo.LinearHeapPrograms.Examples
open HeapLeases ScopedLend

abbrev graph := Graph.Examples.graph

def consume (slot : Nat) (next : Program) : Program := .call slot graph 15 3 next

/-- Two equal payloads still have different owned identities; consume the older
slot first to exercise removal rather than stack-only consumption. -/
def twoOwners : Program := .allocate 42 (.allocate 42 (consume 1 (consume 0 .done)))

def interleaved : Program := .allocate 42 (.allocate 7
  (consume 1 (.allocate 99 (consume 1 (consume 0 .done)))))

theorem two_checked : Checked 0 twoOwners := check_sound (by decide)
theorem interleaved_checked : Checked 0 interleaved := check_sound (by decide)

theorem two_total : ∃ events t, Runs twoOwners [] empty events t := closed_total two_checked

theorem interleaved_total : ∃ events t, Runs interleaved [] empty events t :=
  closed_total interleaved_checked

theorem two_safe (run : Runs twoOwners [] empty events t) :
    Steps empty events t ∧ Valid t ∧ t.lease = empty.lease ∧
    ∀ x ∈ allocations events, (released events).count x = 1 ∧ t.live x = false :=
  closed_safety two_checked run

def first : State := allocatedState empty 42
def second : State := allocatedState first 42
def afterOlder : State := finalState second 0 42 .free
def finished : State := finalState afterOlder 1 42 .free

theorem older_call : Graph.CoreRuns graph 15 3 second 0 42
    [.beginLease 0 0, .read 0 42, .close 0, .free 0] afterOlder :=
  .lend (readRoot := 8) (rest := 11) (k := .free) rfl rfl
    (.read (a := 4) (i := 6) (p := 7) rfl rfl rfl rfl)

theorem newer_call : Graph.CoreRuns graph 15 3 afterOlder 1 42
    [.beginLease 1 1, .read 1 42, .close 1, .free 1] finished :=
  .lend (readRoot := 8) (rest := 11) (k := .free) rfl rfl
    (.read (a := 4) (i := 6) (p := 7) rfl rfl rfl rfl)

theorem concrete_run : Runs twoOwners [] empty
    [.alloc 0 42, .alloc 1 42, .beginLease 0 0, .read 0 42, .close 0, .free 0,
     .beginLease 1 1, .read 1 42, .close 1, .free 1] finished :=
  .allocate (.allocate (.call (.there .here) older_call (.call .here newer_call .done)))

theorem equal_payloads_distinct : second.payload 0 = second.payload 1 ∧
    Owns second [1, 0] := by
  exact ⟨rfl, allocate_owns (step_valid empty_valid Step.alloc) (allocate_owns empty_valid empty_owns)⟩

theorem older_dead_newer_live : afterOlder.live 0 = false ∧ afterOlder.live 1 = true := by decide

theorem all_freed : finished.live 0 = false ∧ finished.live 1 = false := by decide

theorem duplicate_capability_rejected : ¬ Owns second [0, 0] := by
  intro h
  have := h.distinct
  simp at this

theorem leak_rejected : check 0 (.allocate 42 .done) = false := by decide

theorem use_after_consume_rejected :
    check 0 (.allocate 42 (consume 0 (consume 0 .done))) = false := by decide

theorem wrong_slot_rejected : check 0 (.allocate 42 (consume 1 .done)) = false := by decide

theorem invalid_callee_rejected :
    check 0 (.allocate 42 (.call 0 graph 15 2 .done)) = false := by decide

/-- Removing a middle capability preserves two unrelated identities. -/
theorem middle_selection : Select [3, 2, 1] 1 2 [3, 1] := .there .here

theorem borrowed_capability_rejected : ¬ Owns (opened second 0) [0] := by
  intro h
  exact h.leaseFree 0 (by simp) 0 rfl

theorem closed_no_live_objects (run : Runs interleaved [] empty events t) :
    ∀ x, t.live x = false := closed_heap_empty interleaved_checked run

theorem ambient_owns : Owns ScopedLend.Examples.initial [1] := by
  constructor
  · simp
  · intro x member; simp only [List.mem_singleton] at member; subst x; decide
  · intro x member; simp only [List.mem_singleton] at member; subst x
    exact ScopedLend.Examples.owner_available

theorem ambient_borrow_survives
    (run : Runs (consume 0 .done) [1] ScopedLend.Examples.initial events t) :
    t.lease 0 = some 0 ∧ t.live 0 = true ∧ t.live 1 = false := by
  have checked : Checked 1 (consume 0 .done) := check_sound (by decide)
  have frame := lease_frame checked run
  have valid := (execution_safe checked rfl ScopedLend.Examples.initial_valid ambient_owns run).2
  have lease : t.lease 0 = some 0 := by rw [frame]; rfl
  exact ⟨lease, (valid.leased _ _ lease).2,
    (no_tracked_leaks checked rfl ScopedLend.Examples.initial_valid ambient_owns run
      (Or.inl (by simp))).2⟩

end Jihoo.LinearHeapPrograms.Examples
