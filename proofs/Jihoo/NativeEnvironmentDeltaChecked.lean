import Jihoo.NativeEnvironmentDelta
import Jihoo.NativeUnifiedProgram

/-! Checked mixed histories authenticate the environment used by delta conversion. -/
namespace Jihoo.NativeKernel.EnvironmentDelta

private theorem lookup_push {array : Array α} {added selected : α} {index : Nat}
    (found : (array.push added)[index]? = some selected) : array[index]? = some selected ∨ selected = added := by
  by_cases earlier : index < array.size
  · apply Or.inl
    rw [Array.getElem?_eq_getElem earlier]
    simpa only [Array.getElem?_push_lt earlier] using found
  · obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
    have last : index = array.size := by simp only [Array.size_push] at inside; omega
    subst index
    rw [Array.getElem?_push_size] at found
    exact Or.inr (Option.some.inj found).symm

theorem checked_globals_transparent
    (history : UnifiedProgram.UnifiedProgramChecked definitions families env) :
    ∀ (index : Nat) (declaration : Environment.GlobalDeclaration), env.globals[index]? = some declaration →
      GlobalEnvironment.GlobalFree declaration.type ∧ GlobalEnvironment.GlobalFree declaration.value := by
  induction history with
  | empty =>
      intro index declaration found
      obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp found
      exact False.elim (Nat.not_lt_zero index inside)
  | definition history checked ih =>
      intro index declaration found
      rcases lookup_push found with earlier | same
      · exact ih _ _ earlier
      · subst declaration
        refine ⟨checked.typeExpansion.globalFree ?_, checked.valueExpansion.globalFree ?_⟩
        all_goals
          intro entry member
          obtain ⟨j, selected⟩ := List.mem_iff_getElem?.mp member
          exact (ih j entry (by simpa using selected)).2
  | family history checked ih => exact ih

theorem Admissible.ofChecked (history : UnifiedProgram.UnifiedProgramChecked definitions families env) :
    Admissible env :=
  ⟨fun index declaration found => (history.wellFormed.globals index declaration found).2.1,
    fun index declaration found => (checked_globals_transparent history index declaration found).2⟩

end Jihoo.NativeKernel.EnvironmentDelta
