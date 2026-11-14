import Jihoo.NativeEnvironmentDeltaConversion
import Jihoo.NativeEnvironmentDeltaChecked
import Jihoo.NativeEnvironmentInversion

/-! The delta root has a genuine original-type ghost preservation theorem for
the existing unified judgment. The checked history supplies the actual body;
no external typing, closedness or preservation certificate is assumed. -/
namespace Jihoo.NativeKernel.EnvironmentDelta

theorem checked_global_preserves
    (history : UnifiedProgram.UnifiedProgramChecked definitions families env)
    (typed : Environment.HasType env ctx mode (.node (.global index) []) type) :
    ∃ declaration, env.globals[index]? = some declaration ∧
      Environment.HasType env ctx true declaration.value type := by
  obtain ⟨declaration, found, converted⟩ := typed.principalView
  obtain ⟨sort, _, bodyTyped⟩ := history.global_typing found
  have renamed : Ghost.Renaming [] ctx id := by
    intro x binding selected
    simp [lookup] at selected
  have body := bodyTyped.ghostRenaming history.wellFormed renamed
  simp only [Term.rename_id] at body
  rw [Environment.closed_rename (history.wellFormed.globals index declaration found).1] at converted
  exact ⟨declaration, found, body.convert converted⟩

end Jihoo.NativeKernel.EnvironmentDelta
