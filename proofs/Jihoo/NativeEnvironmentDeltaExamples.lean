import Jihoo.NativeEnvironmentDeltaBounded
import Jihoo.NativeEnvironmentDeltaTyping

namespace Jihoo.NativeKernel.EnvironmentDelta.Examples

private def global (index : Nat) : Term := .node (.global index) []
private def function : Term := .pi false .u64 .u64
private def identity : Term := .lam false .u64 (.var 0)
private def definitions : List Environment.GlobalDeclaration :=
  [⟨.univ 0, .buffer (.natural 2)⟩, ⟨.univ 0, function⟩,
   ⟨global 1, identity⟩, ⟨.u64, .natural 7⟩]
private def env : Environment :=
  ⟨#[⟨.univ 0, .buffer (.natural 2)⟩, ⟨.univ 0, function⟩,
     ⟨function, identity⟩, ⟨.u64, .natural 7⟩], #[]⟩
private theorem history : UnifiedProgram.UnifiedProgramChecked definitions [] env :=
  UnifiedProgram.checkProgram_sound
    (by cbv : UnifiedProgram.checkProgram 24 24 definitions [] = some env)

theorem authentic_delta_environment : Admissible env := .ofChecked history

theorem buffer_alias_exposed : Bounded.normalize env 16 64 (global 0) = some (.buffer (.natural 2)) := by cbv

theorem function_type_alias_exposed : Bounded.normalize env 16 64 (global 1) = some function := by cbv

theorem delta_then_dependent_beta :
    Bounded.equal env 16 64 (.app (global 2) (global 3)) (.natural 7) = true := by cbv

theorem globals_under_evidence_binder :
    expand env (.lam true (.lt (.var 0) (global 3)) (global 3)) =
      .lam true (.lt (.var 0) (.natural 7)) (.natural 7) := by cbv

theorem repeated_bodies_precharged :
    Bounded.normalize env 16 2 (.uadd (global 3) (global 3)) = none := by cbv

theorem exact_shared_expansion_budget :
    Bounded.normalize env 16 3 (.uadd (global 3) (global 3)) = some (.natural 14) := by cbv

theorem unresolved_global_rejected : Bounded.normalize env 16 64 (global 8) = none := by cbv

theorem malformed_global_rejected :
    Bounded.normalize env 16 64 (.node (.global 0) [.natural 1]) = none := by cbv

theorem delta_root_retains_original_type :
    Environment.HasType env [⟨.u64, true⟩] true (.natural 7) .u64 := by
  have input : Environment.HasType env [⟨.u64, true⟩] false (global 3) .u64 := by
    simpa only [global, Term.rename, renameArgs] using Environment.HasType.global
      (env := env) (ctx := [⟨.u64, true⟩]) (ghost := false) (g := 3)
      (declaration := ⟨.u64, .natural 7⟩) rfl
  obtain ⟨declaration, found, preserved⟩ := checked_global_preserves history input
  have same : declaration = (⟨.u64, .natural 7⟩ : Environment.GlobalDeclaration) := by
    simpa [env] using found.symm
  simpa only [same] using preserved

end Jihoo.NativeKernel.EnvironmentDelta.Examples
