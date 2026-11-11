import Jihoo.SymbolicCoreCompactionTotality
import Jihoo.SymbolicCoreExamples
import Jihoo.SizedErasureCompiler

/-! Structural regressions cover retained dead aliases, erased branch scopes,
natural binders, and lend's retained reader slot. No execution is assumed. -/
namespace Jihoo.SymbolicCoreCompactionChecks
open ScopedLend SymbolicCoreContext SymbolicCoreTyping SizedErasure
open SymbolicCoreCompaction SymbolicCoreExamples

private theorem support_inputs : MaskSupports inputs [true, true, true] := by
  intro k e h
  cases k with
  | zero => cases h; rfl
  | succ k => cases k with
    | zero => cases h; rfl
    | succ k => cases k with
      | zero => cases h; rfl
      | succ k => simp [inputs] at h

/-- This checks allocation, ghost branch, lend scopes, and freeing all aliases. -/
theorem branch_lend_erases : ∃ term, Erases graph [true, true, true] 40 term :=
  typing_erases body_typed support_inputs

theorem natural_binder_erases : ∃ term, Erases dependentGraph [true, true] 6 term := by
  apply typing_erases dependent_result_typed
  intro k e h
  cases k with
  | zero => cases h; rfl
  | succ k => cases k with
    | zero => cases h; rfl
    | succ k => simp [dependentInputs] at h

theorem natural_binder_compiles :
    compileTarget dependentGraph 4 [true, true] 6 =
      some (.app (.var 1) (.allocate (.var 0) (.var 1))) := by
  decide +kernel

private theorem alias_support : MaskSupports [.owner 0, .nat, .owner 0, .owner 1]
    [true, true, true, true] := by
  intro k e h
  match k with
  | 0 | 1 | 2 | 3 => cases h; rfl
  | k+4 => simp at h

theorem transfer_preserves_dead_alias_slots :
    MaskSupports (transferred [.owner 0, .nat, .owner 0, .owner 1] 0)
      [true, true, true, true, true] := alias_support.mapOwners.push rfl

theorem consumed_preserves_dead_alias_slots :
    MaskSupports (consumed 0 [.owner 0, .nat, .owner 0, .owner 1])
      [true, true, true, true] := alias_support.mapOwners

theorem ghost_branch_mask :
    MaskSupports (push (.bound (.var 1) (.var 2)) inputs) [false, true, true, true] :=
  support_inputs.push rfl

theorem lend_reader_retained_dead_mask :
    MaskSupports (push .dead inputs) [true, true, true, true] :=
  support_inputs.push trivial

/-- Dead slots are not required even to have a corresponding runtime value,
matching the deliberately weak existing Agrees relation. -/
theorem absent_dead_supported : MaskSupports [.dead] [] := by
  intro k e h
  cases k with
  | zero => cases h; trivial
  | succ k => simp at h

theorem live_slot_cannot_be_erased : ¬ MaskSupports [.nat] [false] := by
  intro support
  have bad := support 0 .nat rfl
  cases bad

theorem bound_slot_cannot_be_retained :
    ¬ MaskSupports [.bound (.literal 0) (.literal 1)] [true] := by
  intro support
  have bad := support 0 (.bound (.literal 0) (.literal 1)) rfl
  cases bad

def transferGraph : Graph.Graph := #[
  .natural 1, .buffer 0, .var 2, .var 0, .lam false 1 3, .app 4 2]

theorem transfer_typed :
    Typing transferGraph [.owner 0, .nat, .owner 0] [.literal 1] 5 (.owner (.literal 1)) := by
  apply Typing.ownedLet (slot := 0) (n := .literal 1) rfl rfl rfl rfl rfl
  · exact ⟨0, rfl, ⟨.literal rfl (by decide), .literal⟩⟩
  · exact .owner rfl rfl

theorem transfer_compiles :
    compileTarget transferGraph 3 [true, true, true] 5 = some (.app (.var 2) (.var 0)) := by
  decide +kernel

def consumedGraph : Graph.Graph := #[.var 0, .var 2, .free 0 1]

theorem consumed_typed :
    Typing consumedGraph [.owner 0, .owner 0, .scalar] [.literal 1] 2 .scalar := by
  exact .free (slot := 0) rfl rfl rfl (by decide) (.scalar rfl rfl)

/-- Neither dead alias is removed: the scalar keeps runtime slot 2. -/
theorem consumed_compiles :
    compileTarget consumedGraph 3 [true, true, true] 2 = some (.free 0 (.var 2)) := by
  decide +kernel

def nestedIndexGraph : Graph.Graph := #[
  .u64, .natural 1, .var 0, .lam false 0 2, .app 3 1, .integer 0, .alloc 4 5]

theorem nested_index_typed : Typing nestedIndexGraph [] [] 6
    (.owner (.letE (.literal 1) (.var 0))) := by
  exact .allocation rfl
    ⟨.letE rfl rfl rfl (.literal rfl (by decide)) (.var rfl),
      .letE .literal (.var trivial)⟩
    (.literal rfl (by decide))

theorem nested_index_compiles : compileTarget nestedIndexGraph 4 [] 6 =
    some (.allocate (.letE (.literal 1) (.var 0)) (.literal 0)) := by
  decide +kernel

/-- Real closed inputs obtain a fixed target at every sufficiently large fuel
from static typing alone, without a supplied successful compiler call. -/
theorem branch_lend_compile_total (hn : n < 2^64) (hi : i < 2^64) :
    ∃ term bound, ∀ fuel, bound ≤ fuel →
      compileTarget graph fuel (compactEnv (SizedCoreExamples.inputEnv n i fill)).1 40 = some term :=
  typing_compiles_closed body_typed (inputs_close hn hi) (SizedCoreExamples.input_agrees n i fill)

theorem natural_binder_compile_total (hn : n < 2^64) :
    ∃ term bound, ∀ fuel, bound ≤ fuel →
      compileTarget dependentGraph fuel (compactEnv [.scalar fill, .nat n]).1 6 = some term :=
  typing_compiles_closed dependent_result_typed (dependent_inputs_close hn) dependent_input_agrees

end Jihoo.SymbolicCoreCompactionChecks
