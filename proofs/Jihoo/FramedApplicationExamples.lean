import Jihoo.FramedOwnedApplications

/-! Actual constructor graphs exercising disjoint producer/frame inventories.
All executions fix their partition plan; no cross-plan uniqueness is claimed. -/
namespace Jihoo.FramedApplicationExamples
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open FramedOwnedApplications

def graph : Graph.Graph := #[
  .natural 1, .buffer 0, .integer 7, .var 0, .var 1, .integer 99,
  .alloc 0 2, .lam false 1 3, .app 7 6, .var 2, .var 3,
  .free 3 4, .lam false 1 11, .app 12 8,
  .free 4 3, .free 9 3, .lam false 1 15, .app 7 3, .app 16 17,
  .free 3 9, .lam false 1 19, .app 20 17,
  .free 3 10, .free 9 22, .lam false 1 23, .app 24 17,
  .lam false 1 14, .app 26 6, .app 20 27,
  .free 3 5, .lam false 1 29, .app 30 17,
  .lam false 1 4, .app 32 17]

def zeroCtx : Context := [.owner 0]
def ctx : Context := [.owner 0, .owner 1, .scalar 0]
def first : State := allocatedState empty 7
def initial : State := allocatedState first 7

theorem valid_graph : Graph.valid graph = true := by decide

theorem allocate_shape : Allocation graph 8 7 3 :=
  .intro 7 6 1 0 2 rfl rfl (by decide) rfl rfl rfl

theorem variable_shape : OwnedArgumentBinding.Shape graph 17 3 3 :=
  .intro 7 1 rfl rfl (by decide)

theorem zero_shape : OwnedCoreApplications.Shape graph 13 8 11 :=
  .intro 12 1 7 6 rfl rfl (by decide) rfl

theorem zero_producer_typed : Typing graph .core .owned (OwnedCallContext.producer zeroCtx 0) 0 0 8 := by
  apply Typing.core
  apply Types.allocate allocate_shape (by decide)
  exact .returnOwner rfl

theorem zero_body_typed : Typing graph .core .owned (OwnedCallContext.body zeroCtx 0) 2 0 11 := by
  apply Typing.core
  apply Types.free (slot := 0) rfl (by decide) (by decide)
  exact .returnOwner rfl

theorem zero_prefix_typed : Typing graph (.apply 0 .core .core) .owned zeroCtx 1 0 13 :=
  .apply zero_shape (by decide) zero_producer_typed zero_body_typed

theorem zero_producer_run : Evaluation graph .core .owned (OwnedCallContext.producer zeroCtx 0)
    8 [] [] first 1 [.alloc 1 7] initial := by
  apply Evaluation.core
  apply Exec.allocate allocate_shape
  exact .returnOwner rfl .here

theorem zero_body_run : Evaluation graph .core .owned (OwnedCallContext.body zeroCtx 0)
    11 [1,0] [] initial 0 [.free 1] (freedState initial 1) := by
  apply Evaluation.core
  apply Exec.free rfl (by decide) .here
  exact .returnOwner rfl .here

theorem zero_prefix_run : Evaluation graph (.apply 0 .core .core) .owned zeroCtx
    13 [0] [] first 0 [.alloc 1 7, .free 1] (freedState initial 1) :=
  .apply zero_shape zero_producer_run zero_body_run

theorem input_producer_typed : Typing graph .core .owned (OwnedCallContext.producer ctx 1) 1 1 17 := by
  apply Typing.core
  apply Types.ownedLet variable_shape (slot := 0) (by decide) (by decide)
  exact .returnOwner rfl

theorem input_producer_run : Evaluation graph .core .owned (OwnedCallContext.producer ctx 1)
    17 [1] [37] initial 1 [] initial := by
  apply Evaluation.core
  apply Exec.ownedLet variable_shape (by decide) .here
  exact .returnOwner rfl .here

theorem keep_input_shape : OwnedCoreApplications.Shape graph 18 17 15 :=
  .intro 16 1 7 3 rfl rfl (by decide) rfl

theorem keep_input_body_typed : Typing graph .core .owned (OwnedCallContext.body ctx 1) 2 1 15 := by
  apply Typing.core
  apply Types.free (slot := 1) rfl (by decide) (by decide)
  exact .returnOwner rfl

theorem keep_input_typed : Typing graph (.apply 1 .core .core) .owned ctx 2 1 18 :=
  .apply keep_input_shape (by decide) input_producer_typed keep_input_body_typed

theorem keep_input_body_run : Evaluation graph .core .owned (OwnedCallContext.body ctx 1)
    15 [1,0] [37] initial 1 [.free 0] (freedState initial 0) := by
  apply Evaluation.core
  apply Exec.free rfl (by decide) (.there .here)
  exact .returnOwner rfl .here

theorem keep_input_run : Evaluation graph (.apply 1 .core .core) .owned ctx
    18 [1,0] [37] initial 1 [.free 0] (freedState initial 0) :=
  by simpa using (Evaluation.apply (ctx := ctx) (owners := [1,0]) (p := 1) keep_input_shape input_producer_run keep_input_body_run)

theorem keep_frame_shape : OwnedCoreApplications.Shape graph 21 17 19 :=
  .intro 20 1 7 3 rfl rfl (by decide) rfl

theorem keep_frame_body_typed : Typing graph .core .owned (OwnedCallContext.body ctx 1) 2 1 19 := by
  apply Typing.core
  apply Types.free (slot := 0) rfl (by decide) (by decide)
  exact .returnOwner rfl

theorem keep_frame_typed : Typing graph (.apply 1 .core .core) .owned ctx 2 1 21 :=
  .apply keep_frame_shape (by decide) input_producer_typed keep_frame_body_typed

theorem keep_frame_body_run (s : State) (result : Nat) :
    Evaluation graph .core .owned (OwnedCallContext.body ctx 1)
      19 [result,0] [37] s 0 [.free result] (freedState s result) := by
  apply Evaluation.core
  apply Exec.free rfl (by decide) .here
  exact .returnOwner rfl .here

theorem keep_frame_run : Evaluation graph (.apply 1 .core .core) .owned ctx
    21 [1,0] [37] initial 0 [.free 1] (freedState initial 1) :=
  by simpa using (Evaluation.apply (ctx := ctx) (owners := [1,0]) (p := 1) keep_frame_shape input_producer_run (keep_frame_body_run initial 1))

theorem scalar_shape : OwnedCoreApplications.Shape graph 25 17 23 :=
  .intro 24 1 7 3 rfl rfl (by decide) rfl

theorem scalar_body_typed : Typing graph .core .scalar (OwnedCallContext.body ctx 1) 2 1 23 := by
  apply Typing.core
  apply Types.free (slot := 1) rfl (by decide) (by decide)
  apply Types.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) trivial

theorem scalar_capture_typed : Typing graph (.apply 1 .core .core) .scalar ctx 2 1 25 :=
  .apply scalar_shape (by decide) input_producer_typed scalar_body_typed

theorem scalar_body_run : Evaluation graph .core .scalar (OwnedCallContext.body ctx 1)
    23 [1,0] [37] initial 37 [.free 0, .free 1]
    (freedState (freedState initial 0) 1) := by
  apply Evaluation.core
  apply Exec.free rfl (by decide) (.there .here)
  apply Exec.free rfl (by decide) .here
  exact .finish rfl rfl

theorem scalar_capture_run : Evaluation graph (.apply 1 .core .core) .scalar ctx
    25 [1,0] [37] initial 37 [.free 0, .free 1]
    (freedState (freedState initial 0) 1) :=
  by simpa using (Evaluation.apply (ctx := ctx) (owners := [1,0]) (p := 1) scalar_shape input_producer_run scalar_body_run)

theorem replacement_shape : Allocation graph 27 7 14 :=
  .intro 26 6 1 0 2 rfl rfl (by decide) rfl rfl rfl

theorem replacement_typed : Typing graph .core .owned (OwnedCallContext.producer ctx 1) 1 1 27 := by
  apply Typing.core
  apply Types.allocate replacement_shape (by decide)
  apply Types.free (slot := 1) rfl (by decide) (by decide)
  exact .returnOwner rfl

theorem replacement_run : Evaluation graph .core .owned (OwnedCallContext.producer ctx 1)
    27 [1] [37] initial 2 [.alloc 2 7, .free 1]
    (freedState (allocatedState initial 7) 1) := by
  apply Evaluation.core
  apply Exec.allocate replacement_shape
  apply Exec.free rfl (by decide) (.there .here)
  exact .returnOwner rfl .here

theorem replacement_call_shape : OwnedCoreApplications.Shape graph 28 27 19 :=
  .intro 20 1 26 6 rfl rfl (by decide) rfl

theorem replacement_call_typed : Typing graph (.apply 1 .core .core) .owned ctx 2 1 28 :=
  .apply replacement_call_shape (by decide) replacement_typed keep_frame_body_typed

theorem replacement_call_run : Evaluation graph (.apply 1 .core .core) .owned ctx
    28 [1,0] [37] initial 0 [.alloc 2 7, .free 1, .free 2]
    (freedState (freedState (allocatedState initial 7) 1) 2) :=
  by simpa using (Evaluation.apply (ctx := ctx) (owners := [1,0]) (p := 1) replacement_call_shape replacement_run (keep_frame_body_run _ 2))

theorem equal_payload_different_identities :
    (allocatedState initial 7).payload 0 = (allocatedState initial 7).payload 2 ∧ (0 : Nat) ≠ 2 := by decide

theorem held_frame_unchanged_during_producer :
    (freedState (allocatedState initial 7) 1).live 0 = initial.live 0 ∧
    (freedState (allocatedState initial 7) 1).payload 0 = initial.payload 0 := by decide

theorem producer_frame_hidden : ownerSlot graph (OwnedCallContext.producer ctx 1) 4 = none := rfl

theorem consumed_alias_hidden : ownerSlot graph (OwnedCallContext.body ctx 1) 4 = none := rfl

theorem body_frame_retains_identity :
    (LinearCoreCallers.bindings (ownerView (OwnedCallContext.body ctx 1)) [2,0])[2]? = some (some 0) := rfl

theorem full_shape : OwnedCoreApplications.Shape graph 31 17 29 :=
  .intro 30 1 7 3 rfl rfl (by decide) rfl

theorem full_prefix_typed : Typing graph (.apply 1 .core .core) .scalar zeroCtx 1 0 31 := by
  apply Typing.apply full_shape (by decide)
  · apply Typing.core
    apply Types.ownedLet variable_shape (slot := 0) (by decide) (by decide)
    exact .returnOwner rfl
  · apply Typing.core
    apply Types.free (slot := 0) rfl (by decide) (by decide)
    exact .finish rfl (by decide) (by change 99 < 2^63; decide)

theorem out_of_bounds_partition_rejected : ¬ Typing graph (.apply 2 .core .core) .scalar zeroCtx 1 0 31 := by
  intro typed
  cases typed with
  | apply _ bound _ _ => omega

theorem scalar_capture_all_runs
    (run : Evaluation graph (.apply 1 .core .core) .scalar ctx 25 [1,0] [37] initial value events t) :
    value = 37 ∧ events = [.free 0, .free 1] ∧ t = freedState (freedState initial 0) 1 :=
  run.deterministic scalar_capture_run

theorem stale_body_rejected :
    ¬ Typing graph .core .owned (OwnedCallContext.body zeroCtx 1) 1 0 4 := by
  intro typed
  cases typed with
  | core typed =>
      have resolved := (OwnedCoreApplications.Typing.owned_variable_inversion
        (OwnedCoreApplications.Typing.core typed) (k := 1) rfl).2
      contradiction

theorem stale_call_shape : OwnedCoreApplications.Shape graph 33 17 4 :=
  .intro 32 1 7 3 rfl rfl (by decide) rfl

theorem stale_call_rejected :
    ¬ Typing graph (.apply 1 .core .core) .owned zeroCtx 1 0 33 := by
  intro typed
  exact stale_body_rejected (typed.apply_inversion stale_call_shape).2.2

theorem first_valid : Valid first := step_valid empty_valid .alloc

theorem initial_valid : Valid initial := step_valid first_valid .alloc

theorem initial_owned : Owns initial [1,0] :=
  allocate_owns first_valid (allocate_owns empty_valid empty_owns)

theorem scalar_capture_all_runs_safe
    (run : Evaluation graph (.apply 1 .core .core) .scalar ctx 25 [1,0] [37] initial value events t) :
    Steps initial events t ∧ Valid t ∧ Owns t [] :=
  execution_safe scalar_capture_typed rfl rfl initial_valid initial_owned run

theorem full_prefix_producer_run :
    Evaluation graph .core .owned (OwnedCallContext.producer zeroCtx 1) 17 [0] [] first 0 [] first := by
  apply Evaluation.core
  apply Exec.ownedLet variable_shape (by decide) .here
  exact .returnOwner rfl .here

theorem full_prefix_body_run :
    Evaluation graph .core .scalar (OwnedCallContext.body zeroCtx 1) 29 [0] [] first 99 [.free 0]
      (freedState first 0) := by
  apply Evaluation.core
  apply Exec.free rfl (by decide) .here
  exact .finish rfl rfl

theorem full_prefix_run :
    Evaluation graph (.apply 1 .core .core) .scalar zeroCtx 31 [0] [] first 99 [.free 0]
      (freedState first 0) := by
  simpa using (Evaluation.apply (ctx := zeroCtx) (owners := [0]) (p := 1)
    full_shape full_prefix_producer_run full_prefix_body_run)

end Jihoo.FramedApplicationExamples
