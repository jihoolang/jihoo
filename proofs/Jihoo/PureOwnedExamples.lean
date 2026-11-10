import Jihoo.PureOwnedScalarBridge
import Jihoo.OwnedCoreValues
import Jihoo.PureOwnedEnvironment

/-! Concrete original graph: a nested pure argument captures scalar37 rather
than inner scalar11, then a common scalarLet shifts the lexical owner and frees
it exactly once. Pure arguments never acquire an owner capability. -/
namespace Jihoo.PureOwnedScalar.Examples
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open CoreBridge (Raw)

def graph : Graph.Graph := #[
  .i64, .var 2, .var 1, .lam false 0 2, .app 3 1,
  .lam false 0 4, .app 5 1, .var 0, .free 2 7,
  .lam false 0 8, .app 9 6, .app 9 7, .free 7 7]
def ctx : Context := [.owner 0, .scalar 0, .scalar 1]
def values : List Nat := [11, 37]
def raw : Raw := .app (.lam false .i64 (.app (.lam false .i64 (.var 1)) (.var 2))) (.var 2)
def closed : Raw := .app (.lam false .i64 (.app (.lam false .i64 (.var 1)) (.integer 11))) (.integer 37)

theorem valid_graph : Graph.valid graph = true := by decide

theorem inner_shape : Shape graph 4 1 2 := .intro 3 0 rfl rfl rfl
theorem outer_shape : Shape graph 6 1 4 := .intro 5 0 rfl rfl rfl
theorem continuation_shape : Shape graph 10 6 8 := .intro 9 0 rfl rfl rfl

theorem argument_represents : Represents graph ctx 2 6 raw := by
  apply Represents.app outer_shape
  · exact .scalar (slot := 1) rfl (by decide) (by decide)
  · apply Represents.app inner_shape
    · exact .scalar (slot := 1) rfl (by decide) (by decide)
    · exact .scalar (slot := 1) rfl (by decide) (by decide)

theorem argument_evaluates : Eval graph ctx 6 values 37 := by
  apply Eval.app (a := 37) outer_shape
  · exact .scalar (slot := 1) rfl (by decide) rfl
  · apply Eval.app (a := 11) inner_shape
    · exact .scalar (slot := 1) rfl (by decide) rfl
    · exact .scalar (slot := 1) rfl (by decide) rfl

theorem older_capture_not_latest (run : Eval graph ctx 6 values v) : v = 37 :=
  run.deterministic argument_evaluates

theorem typed_program : Typed graph ctx 1 2 10 := by
  apply Typed.scalarLet continuation_shape argument_represents
  apply Typed.free (slot := 0) rfl (by decide) (by decide)
  exact .finish rfl (by decide) (by trivial)

theorem bind_preserves_owner_identity :
    LinearCoreCallers.bindings (ownerView (bindScalar ctx)) [0] = [none, some 0, none, none] := rfl

theorem bind_retains_distinct_scalar_values :
    scalarBindings (bindScalar ctx) [37, 11, 37] = [some 37, none, some 11, some 37] := rfl

def initial : State := allocatedState empty 7

theorem initial_valid : Valid initial := step_valid empty_valid .alloc

theorem initial_owns : Owns initial [0] := allocate_owns empty_valid empty_owns

theorem concrete_execution : Runs graph ctx 10 [0] values initial 37 [.free 0] (freedState initial 0) := by
  apply Runs.scalarLet continuation_shape argument_evaluates
  apply Runs.free rfl (by decide) .here
  exact .finish rfl rfl

theorem all_runs_return_captured (run : Runs graph ctx 10 [0] values initial v es t) :
    v = 37 ∧ es = [.free 0] ∧ t = freedState initial 0 :=
  run.deterministic concrete_execution

theorem all_runs_safe (run : Runs graph ctx 10 [0] values initial v es t) :
    Steps initial es t ∧ Valid t ∧ Owns t [] :=
  execution_safe typed_program rfl rfl initial_valid initial_owns run

theorem every_run_frees_owner (run : Runs graph ctx 10 [0] values initial v es t) : t.live 0 = false := by
  rw [(all_runs_return_captured run).2.2]
  rfl

theorem raw_typed : CoreBridge.Raw.Beta.HasType (pureContext ctx) raw .i64 :=
  represented_typed valid_graph argument_represents

theorem ready : Ready ctx values := by
  intro k slot lookup
  cases k with
  | zero => simp [ctx] at lookup
  | succ k => cases k with
    | zero => simp [ctx] at lookup; subst slot; exact ⟨11, rfl, by decide⟩
    | succ k => cases k with
      | zero => simp [ctx] at lookup; subst slot; exact ⟨37, rfl, by decide⟩
      | succ k => simp [ctx] at lookup

theorem ready_after_bind_and_free : Ready (consumed 0 (bindScalar ctx)) [37, 11, 37] :=
  (ready.bindScalar (by decide : 37 < 2^63)).consumed

theorem ready_after_owned_and_scalar_results :
    Ready (scalarReturned (ownedReturned ctx 0) 1) [99, 11, 37] :=
  ready.ownedReturned.scalarReturned (by decide : 99 < 2^63)

theorem common_rule_pure_execution : ∃ term : Raw,
    CoreBridge.Raw.Beta.HasType (fun _ => none) (term.subst (closing ctx values)) .i64 ∧
    CoreBridge.Raw.Beta.Evaluation.Steps (term.subst (closing ctx values)) (.integer 37) ∧
    Runs graph (bindScalar ctx) 8 [0] [37, 11, 37] initial 37 [.free 0] (freedState initial 0) := by
  obtain ⟨term, computed, _, evaluated, typed, steps, suffix⟩ :=
    OwnedCoreValues.scalarLet_pure_execution valid_graph typed_program continuation_shape ready concrete_execution
  have eq := evaluated.deterministic argument_evaluates
  subst computed
  exact ⟨term, typed, steps, suffix⟩

theorem closing_exact : raw.subst (closing ctx values) = closed := by
  simp [raw, closed, Raw.subst, Raw.liftSub, Raw.rename, closing, ctx, values, scalarBindings, ScalarCoreCallers.scalarBindings]

theorem closed_typed : CoreBridge.Raw.Beta.HasType (fun _ => none) closed .i64 := by
  have h := close_typed raw_typed ready
  simpa only [closing_exact, CoreBridge.Raw.subst] using h

/-- Explicit strict beta steps, not merely an assumed convergence premise. -/
theorem raw_execution : CoreBridge.Raw.Beta.Evaluation.Steps closed (.integer 37) := by
  apply CoreBridge.Raw.Beta.Evaluation.Steps.next (CoreBridge.Raw.Beta.Evaluation.Step.betaRuntime (.integer 37))
  simpa [Raw.subst, Raw.liftSub, Raw.single, Raw.rename] using
    (CoreBridge.Raw.Beta.Evaluation.Steps.next
      (CoreBridge.Raw.Beta.Evaluation.Step.betaRuntime (A := Raw.i64) (body := Raw.integer 37) (.integer 11))
      CoreBridge.Raw.Beta.Evaluation.Steps.refl)

theorem bridge_execution : CoreBridge.Raw.Beta.Evaluation.Steps
    (raw.subst (closing ctx values)) (.integer 37) :=
  execution argument_represents argument_evaluates

theorem owner_cannot_be_pure {t : Raw} : ¬ Represents graph ctx 2 7 t := by
  intro h
  cases h with
  | integer shape => cases shape
  | scalar shape lookup bound =>
      simp [graph, Graph.nodeAt] at shape
      subst_vars
      simp [ctx] at lookup
  | app shape _ _ =>
      obtain ⟨f, head⟩ := shape.head
      simp [graph, Graph.nodeAt] at head

theorem owner_argument_rejected : ¬ Typed graph ctx 1 2 11 := by
  intro typed
  obtain ⟨raw, represented, _⟩ := typed.scalarLet_inversion (Shape.intro 9 0 rfl rfl rfl)
  exact owner_cannot_be_pure represented

theorem scalar_cannot_be_freed : ¬ Typed graph (bindScalar ctx) 1 3 12 := by
  intro typed
  obtain ⟨slot, lookup, _⟩ := typed.free_inversion (show Graph.nodeAt graph 12 = .free 7 7 from rfl)
  have absent : ownerSlot graph (bindScalar ctx) 7 = none := rfl
  rw [absent] at lookup
  contradiction

end Jihoo.PureOwnedScalar.Examples
