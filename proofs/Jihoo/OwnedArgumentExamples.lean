import Jihoo.OwnedArgumentExecution

/-! Direct variable transfers preserve identities, not lexical aliases. The
entry context has the duplicate owner names introduced by a scalar Lend; no
claim that arbitrary raw contexts establish native checker acceptance is made. -/
namespace Jihoo.OwnedArgumentBinding.Examples
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation

def graph : Graph.Graph := #[
  .natural 1, .buffer 0, .var 0, .var 1, .var 4, .var 6,
  .free 2 5, .free 3 6, .lam false 1 7, .app 8 4,
  .lam false 1 9, .app 10 2,
  .free 3 5, .free 2 12, .lam false 1 13, .app 14 4,
  .lam false 1 15, .app 16 2,
  .var 2, .free 18 5, .i64, .lam false 20 7, .app 21 2,
  .lam true 1 7, .app 23 2]
def ctx : Context := scalarReturned [.owner 0, .owner 1, .scalar 0] 0
def first : Context := transferred ctx 0
def second : Context := transferred first 1
def values : List Nat := [11, 37]

theorem valid_graph : Graph.valid graph = true := by decide

theorem lend_alias_context : ctx = [.owner 0, .scalar 0, .owner 0, .owner 1, .scalar 1] := rfl

theorem all_selected_aliases_dead : first = [.owner 0, .dead, .scalar 0, .dead, .owner 1, .scalar 1] := rfl

theorem nested_transfer_context : second = [.owner 1, .owner 0, .dead, .scalar 0, .dead, .dead, .scalar 1] := rfl

theorem first_shape : Shape graph 11 2 9 := .intro 10 1 rfl rfl (by decide)
theorem second_shape : Shape graph 9 4 7 := .intro 8 1 rfl rfl (by decide)
theorem reverse_first_shape : Shape graph 17 2 15 := .intro 16 1 rfl rfl (by decide)
theorem reverse_second_shape : Shape graph 15 4 13 := .intro 14 1 rfl rfl (by decide)

theorem typed_program : Typed graph ctx 2 2 11 := by
  apply Typed.ownedLet first_shape (slot := 0) (by decide) (by decide)
  apply Typed.ownedLet second_shape (slot := 1) (by decide) (by decide)
  apply Typed.free (slot := 0) rfl (by decide) (by decide)
  apply Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by trivial)

theorem typed_reverse : Typed graph ctx 2 2 17 := by
  apply Typed.ownedLet reverse_first_shape (slot := 0) (by decide) (by decide)
  apply Typed.ownedLet reverse_second_shape (slot := 1) (by decide) (by decide)
  apply Typed.free (slot := 1) rfl (by decide) (by decide)
  apply Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by trivial)

def initial : State := allocatedState (allocatedState empty 7) 7

theorem initial_valid : Valid initial := step_valid (step_valid empty_valid .alloc) .alloc

theorem initial_owns : Owns initial [1, 0] :=
  allocate_owns (step_valid empty_valid .alloc) (allocate_owns empty_valid empty_owns)

theorem equal_payload_distinct_identities : initial.payload 0 = initial.payload 1 ∧ (0 : Nat) ≠ 1 := by decide

theorem bindings_exact : LinearCoreCallers.bindings (ownerView second) [1, 0] =
    [some 0, some 1, none, none, none, none, none] := rfl

theorem captured_scalars_exact : scalarBindings second values =
    [none, none, none, some 11, none, none, some 37] := rfl

theorem concrete_execution : Runs graph ctx 11 [1, 0] values initial 37 [.free 1, .free 0]
    (freedState (freedState initial 1) 0) := by
  apply Runs.ownedLet first_shape (by decide) .here
  apply Runs.ownedLet second_shape (by decide) (.there .here)
  apply Runs.free rfl (by decide) .here
  apply Runs.free rfl (by decide) .here
  exact .finish rfl rfl

theorem reverse_execution : Runs graph ctx 17 [1, 0] values initial 37 [.free 0, .free 1]
    (freedState (freedState initial 0) 1) := by
  apply Runs.ownedLet reverse_first_shape (by decide) .here
  apply Runs.ownedLet reverse_second_shape (by decide) (.there .here)
  apply Runs.free rfl (by decide) (.there .here)
  apply Runs.free rfl (by decide) .here
  exact .finish rfl rfl

theorem all_runs_exact (run : Runs graph ctx 11 [1, 0] values initial v es t) :
    v = 37 ∧ es = [.free 1, .free 0] ∧ t = freedState (freedState initial 1) 0 :=
  run.deterministic concrete_execution

theorem all_runs_safe (run : Runs graph ctx 11 [1, 0] values initial v es t) :
    Steps initial es t ∧ Valid t ∧ Owns t [] :=
  execution_safe typed_program rfl rfl initial_valid initial_owns run

theorem reverse_runs_safe (run : Runs graph ctx 17 [1, 0] values initial v es t) :
    Steps initial es t ∧ Valid t ∧ Owns t [] :=
  execution_safe typed_reverse rfl rfl initial_valid initial_owns run

theorem common_transfer : Nonempty (OwnedArgumentExecution.Transfer graph ctx 2 2 2 9
    [1, 0] values initial 37 [.free 1, .free 0] (freedState (freedState initial 1) 0)) :=
  OwnedArgumentExecution.transfer typed_program first_shape rfl concrete_execution

theorem common_safe_transfer : ∃ witness : OwnedArgumentExecution.Transfer graph ctx 2 2 2 9
    [1, 0] values initial 37 [.free 1, .free 0] (freedState (freedState initial 1) 0),
    witness.object = 1 ∧
    (released [.free 1, .free 0]).count witness.object = 1 ∧
    (freedState (freedState initial 1) 0).live witness.object = false := by
  obtain ⟨w, _, _, _, once, dead⟩ := OwnedArgumentExecution.safe_transfer
    typed_program first_shape rfl rfl rfl initial_valid initial_owns concrete_execution
  have lexical : w.lexical = 0 := by
    have h := w.argument_variable
    simpa [graph, Graph.nodeAt] using h.symm
  have identity : w.object = 1 := by
    have h := w.original_identity
    rw [lexical] at h
    simpa [ctx, scalarReturned, LinearCoreCallers.bindings, ownerView,
      ScalarCoreCallers.ownerView] using h.symm
  exact ⟨w, identity, once, dead⟩

theorem old_name_rejected : ¬ Typed graph second 2 2 19 := by
  intro typed
  obtain ⟨slot, lookup, _⟩ := typed.free_inversion (show Graph.nodeAt graph 19 = .free 18 5 from rfl)
  have absent : ownerSlot graph second 18 = none := rfl
  rw [absent] at lookup
  contradiction

theorem double_use_rejected : ¬ Typed graph (consumed 0 second) 1 2 7 := by
  intro typed
  obtain ⟨slot, lookup, _⟩ := typed.free_inversion (show Graph.nodeAt graph 7 = .free 3 6 from rfl)
  have absent : ownerSlot graph (consumed 0 second) 3 = none := rfl
  rw [absent] at lookup
  contradiction

theorem scalar_is_not_owner : ownerSlot graph second 5 = none := rfl

theorem scalar_annotation_rejected : ¬ Shape graph 22 arg body := by
  intro shape
  cases shape with
  | intro f ty head lam buffer =>
    simp [graph, Graph.nodeAt] at head
    obtain ⟨rfl, rfl⟩ := head
    simp [graph, Graph.nodeAt] at lam
    obtain ⟨rfl, rfl⟩ := lam
    simp [Graph.bufferOne, graph, Graph.nodeAt] at buffer

theorem erased_binding_rejected : ¬ Shape graph 24 arg body := by
  intro shape
  cases shape with
  | intro f ty head lam buffer =>
    simp [graph, Graph.nodeAt] at head
    obtain ⟨rfl, rfl⟩ := head
    simp [graph, Graph.nodeAt] at lam

end Jihoo.OwnedArgumentBinding.Examples
