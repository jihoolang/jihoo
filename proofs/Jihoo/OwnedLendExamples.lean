import Jihoo.OwnedLendTyping

namespace Jihoo.OwnedLendTyping.Examples
open HeapLeases ScopedLend LinearHeapPrograms

/-- Reader copies the original payload into a fresh Buffer1; continuation
consumes the new result and the returned original before returning 99. -/
def graph : ScopedLend.Graph.Graph := #[
  .natural 1, .buffer 0, .i64, .ref 1, .var 0,
  .natural 0, .decide 5 0, .index 4 5 6, .alloc 0 7,
  .lam false 3 8, .var 1, .var 2, .integer 99,
  .free 4 12, .free 10 13, .lam false 1 14, .lam false 1 15,
  .lend 4 9 16, .lam false 1 17, .pi false 1 2]

theorem continuation_typed : OwnedCoreContinuation.Typed graph context 2 0 14 := by
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by exact (by decide : 99 < 2^63))

def typed : Typed graph 18 19 :=
  ⟨7, 14, .read 0, by decide, by decide,
    .read rfl (by decide) (by decide), continuation_typed⟩

def originalName : ScopedLend.Graph.Graph := graph.set! 13 (.free 11 12)

theorem original_name_continuation : OwnedCoreContinuation.Typed originalName context 2 0 14 := by
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by exact (by decide : 99 < 2^63))

def originalTyped : Typed originalName 18 19 :=
  ⟨7, 14, .read 0, by decide, by decide,
    .read rfl (by decide) (by decide), original_name_continuation⟩

def reversed : ScopedLend.Graph.Graph := (graph.set! 13 (.free 10 12)).set! 14 (.free 4 13)

theorem reverse_order_continuation : OwnedCoreContinuation.Typed reversed context 2 0 14 := by
  apply OwnedCoreContinuation.Typed.free (slot := 1) rfl (by decide) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by exact (by decide : 99 < 2^63))

def reversedTyped : Typed reversed 18 19 :=
  ⟨7, 14, .read 0, by decide, by decide,
    .read rfl (by decide) (by decide), reverse_order_continuation⟩

theorem consuming_original_clears_both_aliases :
    OwnedScalarContext.consumed 1 context = [.dead, .owner 0, .dead] := rfl

theorem consuming_result_preserves_original_aliases :
    OwnedScalarContext.consumed 0 context = [.owner 0, .dead, .owner 0] := rfl

theorem lexical_identity :
    LinearCoreCallers.bindings (OwnedScalarContext.ownerView context) [1, 0] = [some 0, some 1, some 0] := rfl

def initial : State := allocatedState empty 11

theorem initial_valid : Valid initial := step_valid empty_valid .alloc

theorem initial_owned : Owns initial [0] := allocate_owns empty_valid empty_owns

theorem copying_transfer_is_distinct :
    (OwnedLendTransfer.final initial 11).payload 0 = 11 ∧ (OwnedLendTransfer.final initial 11).payload 1 = 11 ∧
      Owns (OwnedLendTransfer.final initial 11) [1, 0] := by
  exact ⟨by decide, by decide, OwnedLendTransfer.transfer_owns initial_valid initial_owned⟩

theorem source_execution_exists : ∃ value events t, Runs graph 18 19 initial 0 value events t :=
  total typed initial_valid (initial_owned.live 0 (by simp)) (initial_owned.leaseFree 0 (by simp))

def duplicatedResult : ScopedLend.Graph.Graph := graph.set! 13 (.free 10 12)

theorem duplicate_result_rejected : ¬ OwnedCoreContinuation.Typed duplicatedResult context 2 0 14 := by
  intro h
  obtain ⟨slot, resolved, _, rest⟩ := h.free_inversion rfl
  have eq : 0 = slot := by simpa [OwnedScalarContext.ownerSlot, ScalarCoreCallers.ownerSlot, OwnedScalarContext.consumed, duplicatedResult,
    graph, ScopedLend.Graph.nodeAt, context] using resolved
  subst slot
  exact OwnedCoreContinuation.dead_owner_rejected rfl (by decide) rest

def duplicatedOriginal : ScopedLend.Graph.Graph := (graph.set! 14 (.free 4 13)).set! 13 (.free 11 12)

theorem duplicate_original_alias_rejected : ¬ OwnedCoreContinuation.Typed duplicatedOriginal context 2 0 14 := by
  intro h
  obtain ⟨slot, resolved, _, rest⟩ := h.free_inversion rfl
  have eq : 1 = slot := by simpa [OwnedScalarContext.ownerSlot, ScalarCoreCallers.ownerSlot, OwnedScalarContext.consumed, duplicatedOriginal,
    graph, ScopedLend.Graph.nodeAt, context] using resolved
  subst slot
  exact OwnedCoreContinuation.dead_owner_rejected rfl (by decide) rest

def omittedOriginal : ScopedLend.Graph.Graph := graph.set! 14 (.free 10 12)

theorem missing_original_rejected : ¬ OwnedCoreContinuation.Typed omittedOriginal context 2 0 14 := by
  intro h
  obtain ⟨slot, resolved, _, rest⟩ := h.free_inversion rfl
  have eq : 0 = slot := by simpa [OwnedScalarContext.ownerSlot, ScalarCoreCallers.ownerSlot, OwnedScalarContext.consumed, omittedOriginal,
    graph, ScopedLend.Graph.nodeAt, context] using resolved
  subst slot
  have impossible := (rest.finish_inversion rfl).1
  contradiction

theorem missing_result_rejected : ¬ OwnedCoreContinuation.Typed graph context 2 0 12 := by
  intro h
  have impossible := (h.finish_inversion rfl).1
  contradiction

theorem borrowed_result_rejected (h : Typed (graph.set! 8 (.var 0)) 18 19) : False := by
  have absent : spine (graph.set! 8 (.var 0)) 18 19 = none := by decide
  have shape := h.shape
  rw [absent] at shape
  contradiction

theorem every_run_releases_both (run : Runs graph 18 19 initial 0 value es t) :
    (released es).count 0 = 1 ∧ (released es).count 1 = 1 ∧
      t.live 0 = false ∧ t.live 1 = false := by
  exact (two_owners_released typed initial_valid (initial_owned.live 0 (by simp))
    (initial_owned.leaseFree 0 (by simp)) run).2

theorem every_run_heap_empty (run : Runs graph 18 19 initial 0 value es t) :
    ∀ x, t.live x = false := by
  apply heap_empty typed initial_valid (initial_owned.live 0 (by simp))
    (initial_owned.leaseFree 0 (by simp)) run
  intro y live
  simpa [initial, allocatedState, empty, put] using live

/-- The continuation typing is compositional: a third allocation is introduced
under both owner binders, then all three identities are consumed. -/
def allocating : ScopedLend.Graph.Graph := graph ++ #[
  .integer 37, .alloc 0 20, .var 0, .var 1, .var 2,
  .free 24 12, .free 23 25, .free 22 26, .lam false 1 27,
  .app 28 21, .lam false 1 29, .lam false 1 30,
  .lend 4 9 31, .lam false 1 32]

theorem allocating_continuation : OwnedCoreContinuation.Typed allocating context 2 0 29 := by
  apply OwnedCoreContinuation.Typed.allocate (value := 37) (body := 27)
    (.intro 28 21 1 0 20 rfl rfl (by decide) rfl rfl rfl) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 1) rfl (by decide) (by decide)
  apply OwnedCoreContinuation.Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by exact (by decide : 99 < 2^63))

def allocatingTyped : Typed allocating 33 19 :=
  ⟨7, 29, .read 0, by decide, by decide,
    .read rfl (by decide) (by decide), allocating_continuation⟩

theorem allocating_run_heap_empty (run : Runs allocating 33 19 initial 0 value es t) :
    ∀ x, t.live x = false := by
  apply heap_empty allocatingTyped initial_valid (initial_owned.live 0 (by simp))
    (initial_owned.leaseFree 0 (by simp)) run
  intro y live
  simpa [initial, allocatedState, empty, put] using live

end Jihoo.OwnedLendTyping.Examples
