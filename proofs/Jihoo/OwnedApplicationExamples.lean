import Jihoo.OwnedCoreApplications

/-! Nonvacuous original Core graphs: recursive argument calls, a producer using
an ambient owner, equal-payload fresh identity, and rejection of an old name in
the capture-free body. The native suite separately checks implementation behavior. -/
namespace Jihoo.OwnedApplicationExamples
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open OwnedCoreApplications

def graph : Graph.Graph := #[
  .natural 1, .buffer 0, .integer 7, .var 0, .var 1, .integer 99,
  .alloc 0 2, .lam false 1 3, .app 7 6,
  .free 3 5, .lam false 1 9, .app 10 8,
  .app 7 8, .app 10 12, .app 7 3, .app 10 14,
  .app 7 14, .free 4 3, .lam false 1 17, .app 18 6,
  .app 10 19, .lam false 1 4, .app 21 8]

def initial : State := allocatedState empty 7

theorem valid_graph : Graph.valid graph = true := by decide

theorem producer_shape : Allocation graph 8 7 3 :=
  .intro 7 6 1 0 2 rfl rfl (by decide) rfl rfl rfl

theorem producer_typed : Typing graph .owned [] 0 0 8 := by
  apply Typing.core
  apply Types.allocate producer_shape (by decide)
  exact .returnOwner rfl

theorem producer_run : Evaluation graph .owned [] 8 [] [] empty 0 [.alloc 0 7] initial := by
  apply Evaluation.core
  apply Exec.allocate producer_shape
  exact .returnOwner rfl .here

theorem consume_typed : Typing graph .scalar OwnedCoreResults.consumerContext 1 0 9 := by
  apply Typing.core
  apply Types.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by change 99 < 2^63; decide)

theorem consume_run (s : State) (x : Nat) :
    Evaluation graph .scalar OwnedCoreResults.consumerContext 9 [x] [] s 99 [.free x] (freedState s x) := by
  apply Evaluation.core
  apply Exec.free rfl (by decide) .here
  exact .finish rfl rfl

theorem call_shape : Shape graph 11 8 9 := .intro 10 1 7 6 rfl rfl (by decide) rfl

theorem call_typed : Typing graph .scalar [] 0 0 11 := .apply call_shape producer_typed consume_typed

theorem call_run : Evaluation graph .scalar [] 11 [] [] empty 99 [.alloc 0 7, .free 0] (freedState initial 0) :=
  .apply call_shape producer_run (consume_run initial 0)

theorem identity_typed : Typing graph .owned OwnedCoreResults.consumerContext 1 0 3 :=
  .core (.returnOwner rfl)

theorem identity_run (s : State) (x : Nat) :
    Evaluation graph .owned OwnedCoreResults.consumerContext 3 [x] [] s x [] s :=
  .core (.returnOwner rfl .here)

theorem nested_producer_shape : Shape graph 12 8 3 := .intro 7 1 7 6 rfl rfl (by decide) rfl

theorem nested_producer_typed : Typing graph .owned [] 0 0 12 :=
  .apply nested_producer_shape producer_typed identity_typed

theorem nested_producer_run : Evaluation graph .owned [] 12 [] [] empty 0 [.alloc 0 7] initial :=
  .apply nested_producer_shape producer_run (identity_run initial 0)

theorem nested_shape : Shape graph 13 12 9 := .intro 10 1 7 8 rfl rfl (by decide) rfl

theorem nested_typed : Typing graph .scalar [] 0 0 13 :=
  .apply nested_shape nested_producer_typed consume_typed

theorem nested_run : Evaluation graph .scalar [] 13 [] [] empty 99 [.alloc 0 7, .free 0] (freedState initial 0) :=
  .apply nested_shape nested_producer_run (consume_run initial 0)

theorem ambient_identity_shape : OwnedArgumentBinding.Shape graph 14 3 3 :=
  .intro 7 1 rfl rfl (by decide)

theorem ambient_producer_typed : Typing graph .owned OwnedCoreResults.consumerContext 1 0 14 := by
  apply Typing.core
  apply Types.ownedLet ambient_identity_shape (slot := 0) (by decide) (by decide)
  exact .returnOwner rfl

theorem ambient_producer_run : Evaluation graph .owned OwnedCoreResults.consumerContext 14 [0] [] initial 0 [] initial := by
  apply Evaluation.core
  apply Exec.ownedLet ambient_identity_shape (by decide) .here
  exact .returnOwner rfl .here

theorem ambient_shape : Shape graph 15 14 9 := .intro 10 1 7 3 rfl rfl (by decide) rfl

theorem ambient_typed : Typing graph .scalar OwnedCoreResults.consumerContext 1 0 15 :=
  .apply ambient_shape ambient_producer_typed consume_typed

theorem ambient_run : Evaluation graph .scalar OwnedCoreResults.consumerContext 15 [0] [] initial 99 [.free 0] (freedState initial 0) :=
  .apply ambient_shape ambient_producer_run (consume_run initial 0)

theorem replacement_shape : Allocation graph 19 7 17 :=
  .intro 18 6 1 0 2 rfl rfl (by decide) rfl rfl rfl

theorem replacement_typed : Typing graph .owned OwnedCoreResults.consumerContext 1 0 19 := by
  apply Typing.core
  apply Types.allocate replacement_shape (by decide)
  apply Types.free (slot := 1) rfl (by decide) (by decide)
  exact .returnOwner rfl

theorem replacement_run : Evaluation graph .owned OwnedCoreResults.consumerContext 19 [0] [] initial 1 [.alloc 1 7, .free 0]
    (freedState (allocatedState initial 7) 0) := by
  apply Evaluation.core
  apply Exec.allocate replacement_shape
  apply Exec.free rfl (by decide) (.there .here)
  exact .returnOwner rfl .here

theorem replacement_call_shape : Shape graph 20 19 9 := .intro 10 1 18 6 rfl rfl (by decide) rfl

theorem replacement_call_typed : Typing graph .scalar OwnedCoreResults.consumerContext 1 0 20 :=
  .apply replacement_call_shape replacement_typed consume_typed

theorem replacement_call_run : Evaluation graph .scalar OwnedCoreResults.consumerContext 20 [0] [] initial 99
    [.alloc 1 7, .free 0, .free 1] (freedState (freedState (allocatedState initial 7) 0) 1) :=
  .apply replacement_call_shape replacement_run (consume_run _ 1)

theorem equal_payload_not_equal_identity :
    (allocatedState initial 7).payload 0 = (allocatedState initial 7).payload 1 ∧ (0 : Nat) ≠ 1 := by decide

theorem call_all_runs (run : Evaluation graph .scalar [] 13 [] [] empty value events t) :
    value = 99 ∧ events = [.alloc 0 7, .free 0] ∧ t = freedState initial 0 :=
  run.deterministic nested_run

theorem replacement_released_once :
    (released [.alloc 1 7, .free 0, .free 1]).count 0 = 1 ∧
    (released [.alloc 1 7, .free 0, .free 1]).count 1 = 1 := by decide

theorem old_body_name_rejected : ¬ Typing graph .owned OwnedCoreResults.consumerContext 1 0 4 := by
  intro typed
  have resolved := (typed.owned_variable_inversion rfl).2
  contradiction

theorem invalid_capture_shape : Shape graph 22 8 4 := .intro 21 1 7 6 rfl rfl (by decide) rfl

theorem old_capture_call_rejected : ¬ Typing graph .owned [] 0 0 22 := by
  intro typed
  exact old_body_name_rejected (typed.apply_inversion invalid_capture_shape).2

end Jihoo.OwnedApplicationExamples
