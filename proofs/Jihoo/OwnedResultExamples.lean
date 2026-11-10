import Jihoo.OwnedCoreResults

/-! Owned return retains precisely one concrete capability, not an unconsumed
scalar. Equal payloads do not identify allocations. The examples use original
Core graph constructors and the common result-indexed typing/execution judgment. -/
namespace Jihoo.OwnedResultExamples
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation

def graph : Graph.Graph := #[
  .natural 1, .buffer 0, .integer 7, .var 0, .var 1, .var 2,
  .free 3 4, .free 4 3,
  .lam false 1 3, .app 8 3,
  .lam false 1 7, .alloc 0 2, .app 10 11,
  .lam false 1 6, .app 13 11,
  .free 3 3, .free 4 4,
  .integer 99, .free 3 17,
  .free 3 5, .lam false 1 4, .app 20 3,
  .ref 1, .natural 0, .decide 23 0, .index 3 23 24,
  .alloc 0 25, .lam false 22 26, .lam false 1 6, .lam false 1 28,
  .lend 3 27 29, .lam false 1 7, .lam false 1 31, .lend 3 27 32]

def ctx : Context := [.owner 0]
def initial : State := allocatedState empty 7

theorem valid_graph : Graph.valid graph = true := by decide

theorem initial_valid : Valid initial := step_valid empty_valid .alloc

theorem initial_owns : Owns initial [0] := allocate_owns empty_valid empty_owns

theorem identity_shape : OwnedArgumentBinding.Shape graph 9 3 3 :=
  .intro 8 1 rfl rfl (by decide)

theorem fresh_shape : Allocation graph 12 7 7 :=
  .intro 10 11 1 0 2 rfl rfl (by decide) rfl rfl rfl

theorem original_shape : Allocation graph 14 7 6 :=
  .intro 13 11 1 0 2 rfl rfl (by decide) rfl rfl rfl

theorem typed_return_identity : OwnedTyped graph ctx 1 0 9 := by
  apply Types.ownedLet identity_shape (slot := 0) (by decide) (by decide)
  exact .returnOwner rfl

theorem typed_return_fresh : OwnedTyped graph ctx 1 0 12 := by
  apply Types.allocate fresh_shape (by decide)
  apply Types.free (slot := 1) rfl (by decide) (by decide)
  exact .returnOwner rfl

theorem typed_return_original : OwnedTyped graph ctx 1 0 14 := by
  apply Types.allocate original_shape (by decide)
  apply Types.free (slot := 0) rfl (by decide) (by decide)
  exact .returnOwner rfl

theorem return_identity : OwnedRuns graph ctx 9 [0] [] initial 0 [] initial := by
  apply Exec.ownedLet identity_shape (by decide) .here
  exact .returnOwner rfl .here

theorem return_fresh : OwnedRuns graph ctx 12 [0] [] initial 1 [.alloc 1 7, .free 0]
    (freedState (allocatedState initial 7) 0) := by
  apply Exec.allocate fresh_shape
  apply Exec.free rfl (by decide) (.there .here)
  exact .returnOwner rfl .here

theorem return_original : OwnedRuns graph ctx 14 [0] [] initial 0 [.alloc 1 7, .free 1]
    (freedState (allocatedState initial 7) 1) := by
  apply Exec.allocate original_shape
  apply Exec.free rfl (by decide) .here
  exact .returnOwner rfl .here

theorem equal_payload_different_returns :
    (allocatedState initial 7).payload 0 = (allocatedState initial 7).payload 1 ∧
    (0 : Nat) ≠ 1 := by decide

theorem fresh_result_live_original_dead :
    (freedState (allocatedState initial 7) 0).live 1 = true ∧
    (freedState (allocatedState initial 7) 0).live 0 = false := by decide

theorem original_result_live_fresh_dead :
    (freedState (allocatedState initial 7) 1).live 0 = true ∧
    (freedState (allocatedState initial 7) 1).live 1 = false := by decide

theorem consuming_continuation_typed : Typed graph ctx 1 0 18 := by
  apply Types.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by change 99 < 2^63; decide)

theorem consuming_returned_fresh : Runs graph ctx 18 [1] []
    (freedState (allocatedState initial 7) 0) 99 [.free 1]
    (freedState (freedState (allocatedState initial 7) 0) 1) := by
  apply Exec.free rfl (by decide) .here
  exact .finish rfl rfl

theorem consuming_returned_original : Runs graph ctx 18 [0] []
    (freedState (allocatedState initial 7) 1) 99 [.free 0]
    (freedState (freedState (allocatedState initial 7) 1) 0) := by
  apply Exec.free rfl (by decide) .here
  exact .finish rfl rfl

theorem fresh_composed_release_counts :
    (released ([.alloc 1 7, .free 0] ++ [.free 1])).count 0 = 1 ∧
    (released ([.alloc 1 7, .free 0] ++ [.free 1])).count 1 = 1 := by decide

theorem original_composed_release_counts :
    (released ([.alloc 1 7, .free 1] ++ [.free 0])).count 0 = 1 ∧
    (released ([.alloc 1 7, .free 1] ++ [.free 0])).count 1 = 1 := by decide

private theorem typed_variable (variableShape : Graph.nodeAt g root = .var k)
    (typed : OwnedTyped g context n m root) :
    n = 1 ∧ ownerSlot g context root = some 0 := by
  cases typed with
  | returnOwner lookup => exact ⟨rfl, lookup⟩
  | free head _ _ _ => rw [variableShape] at head; contradiction
  | allocate shape _ _ =>
      cases shape with
      | intro _ _ _ _ _ head _ _ _ _ _ => rw [variableShape] at head; contradiction
  | lend shape _ _ _ _ =>
      obtain ⟨_, _, head⟩ := shape.head
      rw [variableShape] at head; contradiction
  | scalarLend shape _ _ _ _ =>
      obtain ⟨_, _, head⟩ := shape.head
      rw [variableShape] at head; contradiction
  | scalarLet shape _ _ =>
      obtain ⟨_, head⟩ := shape.head
      rw [variableShape] at head; contradiction
  | ownedLet shape _ _ _ =>
      obtain ⟨_, head⟩ := shape.head
      rw [variableShape] at head; contradiction

theorem lost_other_owner_rejected : ¬ OwnedTyped graph [.owner 0, .owner 1] 2 0 3 := by
  intro typed
  have h := (typed_variable (show Graph.nodeAt graph 3 = .var 0 from rfl) typed).1
  contradiction

theorem consumed_owner_return_rejected : ¬ OwnedTyped graph (consumed 0 ctx) 0 0 3 := by
  intro typed
  have h := (typed_variable (show Graph.nodeAt graph 3 = .var 0 from rfl) typed).1
  contradiction

theorem old_alias_return_rejected :
    ¬ OwnedTyped graph (OwnedArgumentBinding.transferred ctx 0) 1 0 4 := by
  intro typed
  have h := (typed_variable (show Graph.nodeAt graph 4 = .var 1 from rfl) typed).2
  have missing : ownerSlot graph (OwnedArgumentBinding.transferred ctx 0) 4 = none := rfl
  rw [missing] at h
  contradiction

theorem scalar_is_not_owned_result : ¬ OwnedTyped graph [.scalar 0] 1 1 3 := by
  intro typed
  have h := (typed_variable (show Graph.nodeAt graph 3 = .var 0 from rfl) typed).2
  have missing : ownerSlot graph [.scalar 0] 3 = none := rfl
  rw [missing] at h
  contradiction

theorem free_then_return_same_rejected : ¬ OwnedTyped graph ctx 1 0 15 := by
  intro typed
  cases typed with
  | returnOwner lookup =>
      simp [ownerSlot, ScalarCoreCallers.ownerSlot, graph, Graph.nodeAt] at lookup
  | free head _ _ body =>
      have eq : Graph.nodeAt graph 15 = .free 3 3 := rfl
      have h := head.symm.trans eq
      cases h
      have impossible := (typed_variable (show Graph.nodeAt graph 3 = .var 0 from rfl) body).1
      contradiction
  | allocate shape _ _ =>
      cases shape with
      | intro _ _ _ _ _ head _ _ _ _ _ => simp [graph, Graph.nodeAt] at head
  | lend shape _ _ _ _ =>
      obtain ⟨_, _, head⟩ := shape.head
      simp [graph, Graph.nodeAt] at head
  | scalarLend shape _ _ _ _ =>
      obtain ⟨_, _, head⟩ := shape.head
      simp [graph, Graph.nodeAt] at head
  | scalarLet shape _ _ =>
      obtain ⟨_, head⟩ := shape.head
      simp [graph, Graph.nodeAt] at head
  | ownedLet shape _ _ _ =>
      obtain ⟨_, head⟩ := shape.head
      simp [graph, Graph.nodeAt] at head

theorem borrowed_fresh_shape : Shape graph 30 3 25 6 :=
  .intro 27 29 22 26 0 1 28 1 rfl rfl (by decide) rfl rfl rfl (by decide) rfl (by decide)

theorem borrowed_original_shape : Shape graph 33 3 25 7 :=
  .intro 27 32 22 26 0 1 31 1 rfl rfl (by decide) rfl rfl rfl (by decide) rfl (by decide)

theorem typed_borrowed_fresh_return : OwnedTyped graph ctx 1 0 30 := by
  apply Types.lend borrowed_fresh_shape (slot := 0) (reader := .read 0) (by decide) (by decide)
    (.read rfl (by decide) (by decide))
  apply Types.free (slot := 1) rfl (by decide) (by decide)
  exact .returnOwner rfl

theorem typed_borrowed_original_return : OwnedTyped graph ctx 1 0 33 := by
  apply Types.lend borrowed_original_shape (slot := 0) (reader := .read 0) (by decide) (by decide)
    (.read rfl (by decide) (by decide))
  apply Types.free (slot := 0) rfl (by decide) (by decide)
  exact .returnOwner rfl

theorem return_borrowed_fresh : OwnedRuns graph ctx 30 [0] [] initial 1
    [.beginLease 0 0, .read 0 7, .alloc 1 7, .close 0, .free 0]
    (freedState (OwnedLendTransfer.final initial 7) 0) := by
  apply Exec.lend borrowed_fresh_shape (by decide) .here (copied := 7) (reads := [.read 0 7])
  · exact .read rfl (by decide) (by decide) (by decide)
  · apply Exec.free rfl (by decide) (.there .here)
    exact .returnOwner rfl .here

theorem return_borrowed_original : OwnedRuns graph ctx 33 [0] [] initial 0
    [.beginLease 0 0, .read 0 7, .alloc 1 7, .close 0, .free 1]
    (freedState (OwnedLendTransfer.final initial 7) 1) := by
  apply Exec.lend borrowed_original_shape (by decide) .here (copied := 7) (reads := [.read 0 7])
  · exact .read rfl (by decide) (by decide) (by decide)
  · apply Exec.free rfl (by decide) .here
    exact .returnOwner rfl .here

theorem borrowed_return_has_no_active_lease (token : Nat) :
    (freedState (OwnedLendTransfer.final initial 7) 0).lease token = none := rfl

theorem consumer_old_name_unavailable : ownerSlot graph ctx 4 = none := rfl

theorem every_fresh_run_same_identity
    (run : OwnedRuns graph ctx 12 [0] [] initial value events final) :
    value = 1 ∧ events = [.alloc 1 7, .free 0] ∧
    final = freedState (allocatedState initial 7) 0 :=
  OwnedCoreResults.OwnedRuns.deterministic run return_fresh

theorem every_original_run_same_identity
    (run : OwnedRuns graph ctx 14 [0] [] initial value events final) :
    value = 0 ∧ events = [.alloc 1 7, .free 1] ∧
    final = freedState (allocatedState initial 7) 1 :=
  OwnedCoreResults.OwnedRuns.deterministic run return_original

theorem every_fresh_run_returns_live_owner
    (run : OwnedRuns graph ctx 12 [0] [] initial value events final) :
    final.live value = true ∧ Unborrowed final value :=
  OwnedCoreResults.returned_live typed_return_fresh rfl rfl initial_valid initial_owns run

theorem every_original_run_returns_live_owner
    (run : OwnedRuns graph ctx 14 [0] [] initial value events final) :
    final.live value = true ∧ Unborrowed final value :=
  OwnedCoreResults.returned_live typed_return_original rfl rfl initial_valid initial_owns run

theorem every_borrowed_return_expires_tokens
    (run : OwnedRuns graph ctx 30 [0] [] initial value events final) (token : Nat) :
    final.lease token = none :=
  OwnedCoreResults.created_tokens_expired initial_valid run (by simp [initial, allocatedState, empty])

theorem initial_coverage : ∀ x, initial.live x = true → x ∈ [0] := by
  intro x live
  simpa [initial, allocatedState, empty, put] using live

theorem every_fresh_run_heap_is_just_result
    (run : OwnedRuns graph ctx 12 [0] [] initial value events final) :
    ∀ x, final.live x = true ↔ x = value :=
  OwnedCoreResults.heap_singleton typed_return_fresh rfl rfl initial_valid initial_owns run initial_coverage

theorem every_original_run_heap_is_just_result
    (run : OwnedRuns graph ctx 14 [0] [] initial value events final) :
    ∀ x, final.live x = true ↔ x = value :=
  OwnedCoreResults.heap_singleton typed_return_original rfl rfl initial_valid initial_owns run initial_coverage

theorem fresh_consumer_execution_exists :
    ∃ owner beforeEvents middle value suffix final,
      OwnedRuns graph ctx 12 [0] [] initial owner beforeEvents middle ∧
      Runs graph OwnedCoreResults.consumerContext 18 [owner] [] middle value suffix final ∧
      Steps initial (beforeEvents ++ suffix) final ∧ Valid final ∧
      (released (beforeEvents ++ suffix)).count owner = 1 ∧ final.live owner = false :=
  OwnedCoreResults.consume_total typed_return_fresh consuming_continuation_typed
    rfl rfl initial_valid initial_owns

theorem fresh_composition_safe
    (produce : OwnedRuns graph ctx 12 [0] [] initial owner beforeEvents middle)
    (consume : Runs graph ctx 18 [owner] [] middle value suffix final) :
    Steps initial (beforeEvents ++ suffix) final ∧ Valid final ∧ Owns final [] ∧
    (released (beforeEvents ++ suffix)).count owner = 1 ∧ final.live owner = false :=
  OwnedCoreResults.consume_safe typed_return_fresh consuming_continuation_typed
    rfl rfl initial_valid initial_owns produce consume

theorem original_composition_safe
    (produce : OwnedRuns graph ctx 14 [0] [] initial owner beforeEvents middle)
    (consume : Runs graph ctx 18 [owner] [] middle value suffix final) :
    Steps initial (beforeEvents ++ suffix) final ∧ Valid final ∧ Owns final [] ∧
    (released (beforeEvents ++ suffix)).count owner = 1 ∧ final.live owner = false :=
  OwnedCoreResults.consume_safe typed_return_original consuming_continuation_typed
    rfl rfl initial_valid initial_owns produce consume

theorem fresh_composition_no_tracked_leaks
    (produce : OwnedRuns graph ctx 12 [0] [] initial owner beforeEvents middle)
    (consume : Runs graph ctx 18 [owner] [] middle value suffix final)
    (tracked : x ∈ [0] ∨ x ∈ allocations (beforeEvents ++ suffix)) :
    (released (beforeEvents ++ suffix)).count x = 1 ∧ final.live x = false :=
  OwnedCoreResults.consume_no_leaks typed_return_fresh consuming_continuation_typed
    rfl rfl initial_valid initial_owns produce consume tracked

theorem original_composition_no_tracked_leaks
    (produce : OwnedRuns graph ctx 14 [0] [] initial owner beforeEvents middle)
    (consume : Runs graph ctx 18 [owner] [] middle value suffix final)
    (tracked : x ∈ [0] ∨ x ∈ allocations (beforeEvents ++ suffix)) :
    (released (beforeEvents ++ suffix)).count x = 1 ∧ final.live x = false :=
  OwnedCoreResults.consume_no_leaks typed_return_original consuming_continuation_typed
    rfl rfl initial_valid initial_owns produce consume tracked

theorem fresh_composition_entire_heap_empty
    (produce : OwnedRuns graph ctx 12 [0] [] initial owner beforeEvents middle)
    (consume : Runs graph ctx 18 [owner] [] middle value suffix final) :
    ∀ x, final.live x = false :=
  OwnedCoreResults.consume_heap_empty typed_return_fresh consuming_continuation_typed
    rfl rfl initial_valid initial_owns produce consume initial_coverage

theorem original_composition_entire_heap_empty
    (produce : OwnedRuns graph ctx 14 [0] [] initial owner beforeEvents middle)
    (consume : Runs graph ctx 18 [owner] [] middle value suffix final) :
    ∀ x, final.live x = false :=
  OwnedCoreResults.consume_heap_empty typed_return_original consuming_continuation_typed
    rfl rfl initial_valid initial_owns produce consume initial_coverage

end Jihoo.OwnedResultExamples
