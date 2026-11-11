import Jihoo.FramedOwnedApplications

/-! Whole-program composition over the exact checked native-exporter snapshot.
The full graph, including checker-created nodes, is compared by the fixture gate.
The source/exporter association remains trusted implementation evidence. -/
namespace Jihoo.ComposedCoreExamples
set_option maxRecDepth 4096
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open FramedOwnedApplications

def root : Nat := 69
def typeRoot : Nat := 0
def graph : Graph.Graph := #[
  .i64,
  .i64,
  .natural 1,
  .buffer 2,
  .natural 1,
  .buffer 4,
  .natural 1,
  .buffer 6,
  .var 2,
  .natural 1,
  .buffer 9,
  .ref 10,
  .var 0,
  .natural 0,
  .natural 0,
  .natural 1,
  .decide 14 15,
  .index 12 13 16,
  .lam false 11 17,
  .i64,
  .natural 1,
  .buffer 20,
  .var 0,
  .natural 1,
  .buffer 23,
  .i64,
  .natural 1,
  .buffer 26,
  .var 0,
  .var 1,
  .free 28 29,
  .lam false 27 30,
  .var 1,
  .app 31 32,
  .lam false 25 33,
  .var 6,
  .app 34 35,
  .lam false 24 36,
  .natural 1,
  .buffer 38,
  .var 0,
  .lam false 39 40,
  .var 2,
  .app 41 42,
  .app 37 43,
  .free 22 44,
  .lam false 21 45,
  .lam false 19 46,
  .lend 8 18 47,
  .lam false 7 48,
  .natural 1,
  .buffer 50,
  .var 0,
  .lam false 51 52,
  .var 0,
  .app 53 54,
  .app 49 55,
  .lam false 5 56,
  .natural 1,
  .integer 7,
  .alloc 58 59,
  .app 57 60,
  .lam false 3 61,
  .natural 1,
  .integer 7,
  .alloc 63 64,
  .app 62 65,
  .lam false 1 66,
  .integer 99,
  .app 67 68,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .ref 3,
  .borrow 8,
  .index 82 13 16,
  .var 3,
  .var 5,
  .app 34 85,
  .lam false 24 86,
  .var 1,
  .app 41 88,
  .app 87 89,
  .free 84 90,
  .lam false 19 91,
  .u64,
  .u64,
  .opaque,
  .opaque,
  .ref 3,
  .u64,
  .u64,
  .opaque,
  .u64,
  .u64,
  .u64,
  .opaque,
  .i64,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .pi false 27 25,
  .pi false 25 25,
  .u64,
  .u64,
  .opaque,
  .pi false 27 25,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .pi false 27 25,
  .pi false 25 25,
  .pi false 24 25,
  .u64,
  .u64,
  .opaque,
  .pi false 39 39,
  .pi false 19 25,
  .borrow 8,
  .index 133 13 16,
  .var 3,
  .var 5,
  .app 34 136,
  .lam false 24 137,
  .var 1,
  .app 41 139,
  .app 138 140,
  .free 135 141,
  .lam false 19 142,
  .u64,
  .u64,
  .opaque,
  .pi false 39 39,
  .u64,
  .u64,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .pi false 27 25,
  .pi false 25 25,
  .pi false 24 25,
  .u64,
  .u64,
  .opaque,
  .pi false 39 39,
  .pi false 7 25,
  .u64,
  .u64,
  .opaque,
  .pi false 51 51,
  .u64,
  .u64,
  .opaque,
  .pi false 51 51,
  .borrow 8,
  .index 171 13 16,
  .var 3,
  .var 5,
  .app 34 174,
  .lam false 24 175,
  .var 1,
  .app 41 177,
  .app 176 178,
  .free 173 179,
  .lam false 19 180,
  .u64,
  .u64,
  .opaque,
  .ref 3,
  .borrow 8,
  .index 186 13 16,
  .var 3,
  .var 5,
  .app 34 189,
  .lam false 24 190,
  .var 1,
  .app 41 192,
  .app 191 193,
  .free 188 194,
  .lam false 19 195,
  .u64,
  .u64,
  .opaque,
  .opaque,
  .ref 3,
  .u64,
  .u64,
  .opaque,
  .u64,
  .u64,
  .u64,
  .opaque,
  .i64,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .pi false 27 25,
  .pi false 25 25,
  .pi false 24 25,
  .u64,
  .u64,
  .opaque,
  .pi false 39 39,
  .pi false 19 25,
  .pi false 7 25,
  .u64,
  .u64,
  .opaque,
  .pi false 51 51,
  .pi false 5 25,
  .u64,
  .u64,
  .i64,
  .i64,
  .buffer 58,
  .borrow 8,
  .index 238 13 16,
  .var 3,
  .var 5,
  .app 34 241,
  .lam false 24 242,
  .var 1,
  .app 41 244,
  .app 243 245,
  .free 240 246,
  .lam false 19 247,
  .u64,
  .u64,
  .opaque,
  .ref 3,
  .borrow 8,
  .index 253 13 16,
  .var 3,
  .var 5,
  .app 34 256,
  .lam false 24 257,
  .var 1,
  .app 41 259,
  .app 258 260,
  .free 255 261,
  .lam false 19 262,
  .u64,
  .u64,
  .opaque,
  .opaque,
  .ref 3,
  .u64,
  .u64,
  .opaque,
  .u64,
  .u64,
  .u64,
  .opaque,
  .i64,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .pi false 27 25,
  .pi false 25 25,
  .pi false 24 25,
  .u64,
  .u64,
  .opaque,
  .pi false 39 39,
  .pi false 19 25,
  .pi false 7 25,
  .u64,
  .u64,
  .opaque,
  .pi false 51 51,
  .u64,
  .u64,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .ref 3,
  .borrow 8,
  .index 306 13 16,
  .var 3,
  .var 5,
  .app 34 309,
  .lam false 24 310,
  .var 1,
  .app 41 312,
  .app 311 313,
  .free 308 314,
  .lam false 19 315,
  .u64,
  .u64,
  .opaque,
  .opaque,
  .ref 3,
  .u64,
  .u64,
  .opaque,
  .u64,
  .u64,
  .u64,
  .opaque,
  .i64,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .opaque,
  .u64,
  .u64,
  .opaque,
  .pi false 27 25,
  .pi false 25 25,
  .pi false 24 25,
  .u64,
  .u64,
  .opaque,
  .pi false 39 39,
  .pi false 19 25,
  .pi false 7 25,
  .u64,
  .u64,
  .opaque,
  .pi false 51 51,
  .pi false 5 25,
  .u64,
  .u64,
  .i64,
  .i64,
  .buffer 58,
  .pi false 3 25,
  .u64,
  .u64,
  .i64,
  .i64,
  .buffer 63,
  .pi false 1 25,
  .i64]

def savedCtx : Context := PureOwnedScalar.bindScalar []
def heldCtx : Context := fresh savedCtx
def inputCtx : Context := fresh heldCtx
def callCtx : Context := OwnedCallContext.body inputCtx 1
def lendCtx : Context := scalarReturned callCtx 1
def freeCtx : Context := consumed 1 lendCtx
def nestedCtx : Context := OwnedCallContext.body freeCtx 1
def chosenCtx : Context := PureOwnedScalar.bindScalar nestedCtx
def movedCtx : Context := OwnedArgumentBinding.transferred chosenCtx 0

def finalPlan : Plan := .free .core
def movePlan : Plan := .ownedLet finalPlan
def chosenPlan : Plan := .scalarLet movePlan
def innerPlan : Plan := .apply 1 (.ownedLet .core) chosenPlan
def afterLendPlan : Plan := .free innerPlan
def lendPlan : Plan := .scalarLend afterLendPlan
def callPlan : Plan := .apply 1 (.ownedLet .core) lendPlan
def inputPlan : Plan := .allocate callPlan
def heldPlan : Plan := .allocate inputPlan
def plan : Plan := .scalarLet heldPlan

theorem valid_graph : Graph.valid graph = true := by decide

theorem saved_shape : PureOwnedScalar.Shape graph root 68 66 := .intro 67 1 rfl rfl rfl

theorem held_shape : Allocation graph 66 7 61 :=
  .intro 62 65 3 63 64 rfl rfl (by decide) rfl rfl rfl

theorem input_shape : Allocation graph 61 7 56 :=
  .intro 57 60 5 58 59 rfl rfl (by decide) rfl rfl rfl

theorem call_shape : OwnedCoreApplications.Shape graph 56 55 48 :=
  .intro 49 7 53 54 rfl rfl (by decide) rfl

theorem producer_shape : OwnedArgumentBinding.Shape graph 55 54 52 := .intro 53 51 rfl rfl (by decide)

theorem lend_shape : ScalarShape graph 48 8 17 45 :=
  .intro 18 47 11 19 46 21 rfl rfl (by decide) rfl rfl rfl (by decide)

theorem inner_shape : OwnedCoreApplications.Shape graph 44 43 36 :=
  .intro 37 24 41 42 rfl rfl (by decide) rfl

theorem inner_producer_shape : OwnedArgumentBinding.Shape graph 43 42 40 := .intro 41 39 rfl rfl (by decide)

theorem chosen_shape : PureOwnedScalar.Shape graph 36 35 33 := .intro 34 25 rfl rfl rfl

theorem move_shape : OwnedArgumentBinding.Shape graph 33 32 30 := .intro 31 27 rfl rfl (by decide)

theorem final_typed : Typing graph finalPlan .scalar movedCtx 1 3 30 := by
  apply Typing.free (slot := 0) rfl (by decide) (by decide)
  exact .core (.finish rfl (by decide) trivial)

theorem move_typed : Typing graph movePlan .scalar chosenCtx 1 3 33 :=
  .ownedLet move_shape (by decide) (by decide) final_typed

theorem chosen_typed : Typing graph chosenPlan .scalar nestedCtx 1 2 36 :=
  .scalarLet chosen_shape (.scalar (slot := 1) rfl (by decide) (by decide)) move_typed

theorem inner_producer_typed : Typing graph (.ownedLet .core) .owned
    (OwnedCallContext.producer freeCtx 1) 1 2 43 := by
  apply Typing.ownedLet inner_producer_shape (slot := 0) (by decide) (by decide)
  exact .core (.returnOwner rfl)

theorem inner_typed : Typing graph innerPlan .scalar freeCtx 1 2 44 :=
  .apply inner_shape (by decide) inner_producer_typed chosen_typed

theorem after_lend_typed : Typing graph afterLendPlan .scalar lendCtx 2 2 45 :=
  .free rfl (by decide) (by decide) inner_typed

theorem lend_typed : Typing graph lendPlan .scalar callCtx 2 1 48 :=
  .scalarLend lend_shape (by decide) (by decide) (.read rfl (by decide) (by decide)) after_lend_typed

theorem producer_typed : Typing graph (.ownedLet .core) .owned
    (OwnedCallContext.producer inputCtx 1) 1 1 55 := by
  apply Typing.ownedLet producer_shape (slot := 0) (by decide) (by decide)
  exact .core (.returnOwner rfl)

theorem call_typed : Typing graph callPlan .scalar inputCtx 2 1 56 :=
  .apply call_shape (by decide) producer_typed lend_typed

theorem input_typed : Typing graph inputPlan .scalar heldCtx 1 1 61 :=
  .allocate input_shape (by decide) call_typed

theorem held_typed : Typing graph heldPlan .scalar savedCtx 0 1 66 :=
  .allocate held_shape (by decide) input_typed

theorem typed_program : Typing graph plan .scalar [] 0 0 root :=
  .scalarLet saved_shape (.integer rfl) held_typed

def heldState : State := allocatedState empty 7
def inputState : State := allocatedState heldState 7
def afterFrame : State := freedState (restored inputState) 0
def finalState : State := freedState afterFrame 1

def events : List Event := [.alloc 0 7, .alloc 1 7, .beginLease 0 0,
  .read 0 7, .close 0, .free 0, .free 1]

theorem final_run : Evaluation graph finalPlan .scalar movedCtx 30 [1] [99,7,99]
    afterFrame 99 [.free 1] finalState := by
  apply Evaluation.free rfl (by decide) .here
  exact .core (.finish rfl rfl)

theorem move_run : Evaluation graph movePlan .scalar chosenCtx 33 [1] [99,7,99]
    afterFrame 99 [.free 1] finalState :=
  .ownedLet move_shape (by decide) .here final_run

theorem chosen_run : Evaluation graph chosenPlan .scalar nestedCtx 36 [1] [7,99]
    afterFrame 99 [.free 1] finalState :=
  .scalarLet chosen_shape (.scalar (slot := 1) rfl (by decide) rfl) move_run

theorem inner_producer_run : Evaluation graph (.ownedLet .core) .owned
    (OwnedCallContext.producer freeCtx 1) 43 [1] [7,99] afterFrame 1 [] afterFrame := by
  apply Evaluation.ownedLet inner_producer_shape (by decide) .here
  exact .core (.returnOwner rfl .here)

theorem inner_run : Evaluation graph innerPlan .scalar freeCtx 44 [1] [7,99]
    afterFrame 99 [.free 1] finalState := by
  simpa [innerPlan] using (Evaluation.apply (ctx := freeCtx) (owners := [1]) (p := 1)
    inner_shape inner_producer_run chosen_run)

theorem after_lend_run : Evaluation graph afterLendPlan .scalar lendCtx 45 [1,0] [7,99]
    (restored inputState) 99 [.free 0, .free 1] finalState :=
  .free rfl (by decide) (.there .here) inner_run

theorem lend_run : Evaluation graph lendPlan .scalar callCtx 48 [1,0] [99]
    inputState 99 [.beginLease 0 0, .read 0 7, .close 0, .free 0, .free 1] finalState := by
  refine Evaluation.scalarLend (copied := 7) (reads := [.read 0 7])
    (suffix := [.free 0, .free 1]) lend_shape (by decide) (.there .here) ?_ after_lend_run
  exact .read rfl (by decide) (by decide) (by simp [opened, put])

theorem producer_run : Evaluation graph (.ownedLet .core) .owned
    (OwnedCallContext.producer inputCtx 1) 55 [1] [99] inputState 1 [] inputState := by
  apply Evaluation.ownedLet producer_shape (by decide) .here
  exact .core (.returnOwner rfl .here)

theorem call_run : Evaluation graph callPlan .scalar inputCtx 56 [1,0] [99]
    inputState 99 [.beginLease 0 0, .read 0 7, .close 0, .free 0, .free 1] finalState := by
  simpa [callPlan] using (Evaluation.apply (ctx := inputCtx) (owners := [1,0]) (p := 1)
    call_shape producer_run lend_run)

theorem input_run : Evaluation graph inputPlan .scalar heldCtx 61 [0] [99] heldState 99
    [.alloc 1 7, .beginLease 0 0, .read 0 7, .close 0, .free 0, .free 1] finalState :=
  .allocate input_shape call_run

theorem held_run : Evaluation graph heldPlan .scalar savedCtx 66 [] [99] empty 99 events finalState :=
  .allocate held_shape input_run

theorem program_run : Evaluation graph plan .scalar [] root [] [] empty 99 events finalState :=
  .scalarLet saved_shape (.integer rfl) held_run

theorem every_run_same
    (run : Evaluation graph plan .scalar [] root [] [] empty v es t) :
    v = 99 ∧ es = events ∧ t = finalState := run.deterministic program_run

theorem every_run_safe
    (run : Evaluation graph plan .scalar [] root [] [] empty v es t) :
    Steps empty es t ∧ Valid t ∧ Owns t [] :=
  execution_safe typed_program rfl rfl empty_valid empty_owns run

theorem every_run_no_live_heap
    (run : Evaluation graph plan .scalar [] root [] [] empty v es t) :
    ∀ x, t.live x = false := by
  have accounted := heap_accounted typed_program rfl rfl empty_valid empty_owns run (by intro x h; cases h)
  intro x
  have absent : t.live x ≠ true := by simpa [OwnedCoreApplications.resultOwners] using (accounted x).mp
  cases h : t.live x
  · rfl
  · exact False.elim (absent h)

theorem distinct_scalar_read_and_return : (7 : Nat) ≠ 99 := by decide

theorem exactly_two_allocations : allocations events = [0,1] := rfl

theorem exactly_two_releases : released events = [0,1] := rfl

theorem no_borrow_after_completion (token : Nat) : finalState.lease token = none := by
  simp [finalState, afterFrame, restored, inputState, heldState, allocatedState, empty, freedState]


/-! Separate compact graph covers the owned-result Lend continuation. It is not
substituted for the exact exporter snapshot above. -/
def ownedGraph : Graph.Graph := #[
  .natural 1, .buffer 0, .ref 1, .integer 7, .var 0, .var 1,
  .integer 99, .alloc 0 3, .lam false 2 7,
  .free 4 6, .free 5 9, .lam false 1 10, .lam false 1 4,
  .app 12 5, .app 11 13, .lam false 1 14, .lam false 1 15,
  .lend 4 8 16, .lam false 1 17, .app 18 7]

def ownedInitialCtx : Context := fresh []
def ownedLendCtx : Context := ownedReturned ownedInitialCtx 0
def ownedBodyCtx : Context := OwnedCallContext.body ownedLendCtx 1
def ownedTailPlan : Plan := .free (.free .core)
def ownedCallPlan : Plan := .apply 1 (.ownedLet .core) ownedTailPlan
def ownedPlan : Plan := .allocate (.lend ownedCallPlan)
def ownedAfter : State := OwnedLendTransfer.final heldState 7
def ownedFinal : State := freedState (freedState ownedAfter 0) 1
def ownedEvents : List Event := [.alloc 0 7, .beginLease 0 0, .alloc 1 7,
  .close 0, .free 0, .free 1]

theorem owned_graph_valid : Graph.valid ownedGraph = true := by decide

theorem owned_allocate_shape : Allocation ownedGraph 19 7 17 :=
  .intro 18 7 1 0 3 rfl rfl (by decide) rfl rfl rfl

theorem owned_lend_shape : OwnedLendContext.Shape ownedGraph 17 4 3 14 :=
  .intro 8 16 2 7 0 1 15 1 rfl rfl (by decide) rfl rfl rfl (by decide) rfl (by decide)

theorem owned_call_shape : OwnedCoreApplications.Shape ownedGraph 14 13 10 :=
  .intro 11 1 12 5 rfl rfl (by decide) rfl

theorem owned_producer_shape : OwnedArgumentBinding.Shape ownedGraph 13 5 4 :=
  .intro 12 1 rfl rfl (by decide)

theorem owned_tail_typed : Typing ownedGraph ownedTailPlan .scalar ownedBodyCtx 2 0 10 := by
  apply Typing.free (slot := 1) rfl (by decide) (by decide)
  apply Typing.free (slot := 0) rfl (by decide) (by decide)
  exact .core (.finish rfl (by decide) (by change 99 < 2^63; decide))

theorem owned_producer_typed : Typing ownedGraph (.ownedLet .core) .owned
    (OwnedCallContext.producer ownedLendCtx 1) 1 0 13 := by
  apply Typing.ownedLet owned_producer_shape (slot := 0) (by decide) (by decide)
  exact .core (.returnOwner rfl)

theorem owned_call_typed : Typing ownedGraph ownedCallPlan .scalar ownedLendCtx 2 0 14 :=
  .apply owned_call_shape (by decide) owned_producer_typed owned_tail_typed

theorem owned_typed_program : Typing ownedGraph ownedPlan .scalar [] 0 0 19 := by
  apply Typing.allocate owned_allocate_shape (by decide)
  exact .lend owned_lend_shape (by decide) (by decide) (.scalar rfl) owned_call_typed

theorem owned_tail_run : Evaluation ownedGraph ownedTailPlan .scalar ownedBodyCtx
    10 [1,0] [] ownedAfter 99 [.free 0, .free 1] ownedFinal := by
  apply Evaluation.free rfl (by decide) (.there .here)
  apply Evaluation.free rfl (by decide) .here
  exact .core (.finish rfl rfl)

theorem owned_producer_run : Evaluation ownedGraph (.ownedLet .core) .owned
    (OwnedCallContext.producer ownedLendCtx 1) 13 [1] [] ownedAfter 1 [] ownedAfter := by
  apply Evaluation.ownedLet owned_producer_shape (by decide) .here
  exact .core (.returnOwner rfl .here)

theorem owned_call_run : Evaluation ownedGraph ownedCallPlan .scalar ownedLendCtx
    14 [1,0] [] ownedAfter 99 [.free 0, .free 1] ownedFinal := by
  simpa [ownedCallPlan] using (Evaluation.apply (ctx := ownedLendCtx) (owners := [1,0]) (p := 1)
    owned_call_shape owned_producer_run owned_tail_run)

theorem owned_program_run : Evaluation ownedGraph ownedPlan .scalar []
    19 [] [] empty 99 ownedEvents ownedFinal := by
  apply Evaluation.allocate owned_allocate_shape
  exact Evaluation.lend (copied := 7) (reads := []) owned_lend_shape (by decide) .here
    (.scalar rfl) owned_call_run

theorem owned_all_runs_same
    (run : Evaluation ownedGraph ownedPlan .scalar [] 19 [] [] empty v es t) :
    v = 99 ∧ es = ownedEvents ∧ t = ownedFinal := run.deterministic owned_program_run

theorem owned_all_runs_safe
    (run : Evaluation ownedGraph ownedPlan .scalar [] 19 [] [] empty v es t) :
    Steps empty es t ∧ Valid t ∧ Owns t [] :=
  execution_safe owned_typed_program rfl rfl empty_valid empty_owns run

theorem owned_all_runs_release_every_object
    (run : Evaluation ownedGraph ownedPlan .scalar [] 19 [] [] empty v es t) :
    (released es).count 0 = 1 ∧ (released es).count 1 = 1 := by
  rw [(owned_all_runs_same run).2.1]
  decide

end Jihoo.ComposedCoreExamples
