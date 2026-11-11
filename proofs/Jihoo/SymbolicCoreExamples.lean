import Jihoo.SymbolicCoreClosing
import Jihoo.SizedCoreExamples

/-! Static regressions have no numeric parameter in their typing derivation.
They reuse the original exporter-tested graph; closure is a later theorem. -/
namespace Jihoo.SymbolicCoreExamples
open ScopedLend SymbolicCoreContext SymbolicCoreTyping
open DependentBufferIndices (Expr)

abbrev graph := DependentBufferGraph.graph

def inputs : Context := [.scalar, .nat, .nat]

/-- One finite derivation checks both branches before n and i are supplied. -/
theorem body_typed : Typing graph inputs [] 40 .scalar := by
  apply Typing.allocate (function := 36) (argument := 39) (domain := 11)
    (length := 37) (init := 38) (n := .var 2) rfl rfl
  · exact ⟨10, rfl, ⟨.var rfl, .var rfl⟩⟩
  · rfl
  · exact ⟨.var rfl, .var rfl⟩
  · exact .var rfl rfl
  · apply Typing.branch (left := 12) (right := 13) (a := .var 2) (b := .var 3) rfl
    · exact ⟨.var rfl, .var rfl⟩
    · exact ⟨.var rfl, .var rfl⟩
    · apply Typing.lend (slot := 0) (n := .var 4) (i := .var 3)
        SizedCoreExamples.read_shape rfl rfl rfl
      · exact ⟨16, rfl, 15, rfl, ⟨.var rfl, .var rfl⟩⟩
      · exact ⟨24, rfl, ⟨.var rfl, .var rfl⟩⟩
      · exact ⟨.var rfl, .var rfl⟩
      · exact .var rfl rfl
      · exact .free (slot := 0) rfl rfl rfl (by decide) (.scalar rfl rfl)
    · exact .free (slot := 0) rfl rfl rfl (by decide) (.literal rfl (by decide))

theorem inputs_close (hn : n < 2^64) (hi : i < 2^64) :
    Closes inputs (SizedCoreExamples.inputContext n i) :=
  .cons trivial (.cons hi (.cons hn .nil))

/-- This is now a corollary of one static derivation, rather than separately
constructing a closing-instance derivation for each pair of input values. -/
theorem all_inputs_typed (hn : n < 2^64) (hi : i < 2^64) :
    SizedCoreTyping.Typing graph (SizedCoreExamples.inputContext n i) [] 40 .scalar :=
  body_typed.instantiate (inputs_close hn hi) .nil trivial

/-- A natural binder appears in the owned result type. Beta instantiation must
replace its index 0 by the argument and lower the remaining lexical indices. -/
def dependentGraph : Graph.Graph := #[
  .u64, .var 1, .var 0, .var 1, .alloc 2 3, .lam false 0 4, .app 5 1]

def dependentInputs : Context := [.scalar, .nat]

theorem dependent_result_typed :
    Typing dependentGraph dependentInputs [] 6 (.owner (.var 1)) := by
  apply Typing.naturalLet (function := 5) (argument := 1) (domain := 0)
    (body := 4) (a := .var 1) (bodyKind := .owner (.var 0)) rfl rfl rfl
  · exact ⟨.var rfl, .var rfl⟩
  · exact .allocation rfl ⟨.var rfl, .var rfl⟩ (.var rfl rfl)

theorem dependent_inputs_close (bound : n < 2^64) :
    Closes dependentInputs [.scalar, .nat n] := .cons trivial (.cons bound .nil)

theorem dependent_all_inputs_typed (bound : n < 2^64) :
    SizedCoreTyping.Typing dependentGraph [.scalar, .nat n] [] 6 (.owner n) :=
  dependent_result_typed.instantiate (dependent_inputs_close bound) .nil rfl

theorem dependent_input_agrees :
    SizedBufferContext.Agrees [.scalar, .nat n] [] [.scalar value, .nat n] := by
  have empty : SizedBufferContext.Agrees [] [] [] :=
    ⟨by simp, by simp, by simp, by simp⟩
  apply empty.bindNat.prepend
  · intros; contradiction
  · intro _; exact ⟨value, rfl⟩
  · intros; contradiction
  · intros; contradiction

theorem dependent_result_run :
    SizedCoreExecution.Eval dependentGraph [.scalar value, .nat n] 6 SizedBufferHeap.empty
      (.owner 0) [.alloc 0 n value] (SizedBufferHeap.allocate SizedBufferHeap.empty n value) :=
  .app rfl rfl (.var rfl rfl) (.allocate rfl (.var rfl rfl) (.var rfl rfl))

/-- Dependent result substitution reaches the actual allocated object, not
only a pure type-expression equality. -/
theorem dependent_result_preserved (bound : n < 2^64)
    (run : SizedCoreExecution.Eval dependentGraph [.scalar value, .nat n] 6
      SizedBufferHeap.empty result events t) :
    result = .owner 0 ∧ t.length 0 = n ∧ LinearHeapPrograms.Owns t.heap [0] ∧
      SizedBufferHeap.Steps SizedBufferHeap.empty events t := by
  have safe := (dependent_all_inputs_typed bound).every_run_safe dependent_input_agrees
    SizedCoreExamples.empty_layout SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns run
  obtain ⟨rfl, rfl, rfl⟩ := run.deterministic dependent_result_run
  exact ⟨rfl, safe.2.2.2, safe.2.2.1, safe.1⟩

/-- End-to-end static typing constructs the safe runtime and release account
without a separately supplied per-input derivation or successful run. -/
theorem body_total (hn : n < 2^64) (hi : i < 2^64) :
    ∃ value events t,
      SizedCoreExecution.Eval graph (SizedCoreExamples.inputEnv n i fill) 40
        SizedBufferHeap.empty value events t ∧
      SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧ SizedBufferHeap.Valid t ∧
      SizedCoreTyping.Post .scalar t value ∧ SizedCoreTyping.Account [] value events := by
  obtain ⟨kind, value, events, t, interpreted, run, steps, valid, post, account⟩ :=
    body_typed.total_accounted (inputs_close hn hi) .nil
      (SizedCoreExamples.input_agrees n i fill) SizedCoreExamples.empty_layout
      SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns
  cases kind <;> simp only [ResultEval] at interpreted
  exact ⟨value, events, t, run, steps, valid, post, account⟩

theorem owner_slot_not_index :
    ¬ Index g [.owner 0] root (.var 0) := by
  intro typed
  cases typed.available with
  | var present => cases present

theorem erased_slot_not_index :
    ¬ Index g [.bound (.literal 0) (.literal 1)] root (.var 0) := by
  intro typed
  cases typed.available with
  | var present => cases present

/-- Direct owned application revokes every old name, including duplicates. -/
theorem transfer_revokes_aliases :
    transferred [.owner 0, .nat, .owner 0, .owner 1] 0 =
      [.owner 0, .dead, .nat, .dead, .owner 1] := by rfl

/-- An erased branch binder shifts the bounds, inventory and result alike. -/
theorem branch_scope_shifts :
    push (.bound (.var 0) (.var 1)) [.nat, .nat] =
      [.bound (.var 1) (.var 2), .nat, .nat] ∧
    shiftSizes [.var 1] = [.var 2] ∧
    shiftResult (.owner (.var 1)) = .owner (.var 2) := by decide

/-- An owner may not supply its own length through unrestricted lookup.
Even a syntactically written malformed input inventory has no admitted closing
interpretation; soundness does not assert nonvacuity of arbitrary contexts. -/
theorem owner_as_length_no_closing
    (closing : Closes [.owner 0] closed) :
    ¬ SizesEval (SizedBufferContext.naturalEnv closed) [.var 0] concrete := by
  intro inventory
  have owner := closing.owner_lookup (k := 0) rfl
  cases inventory with
  | cons length rest =>
      simp [Expr.eval, SizedBufferContext.naturalEnv, owner] at length

end Jihoo.SymbolicCoreExamples
