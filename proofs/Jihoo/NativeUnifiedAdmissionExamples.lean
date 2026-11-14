import Jihoo.NativeUnifiedAdmission

namespace Jihoo.NativeKernel.NativeUnifiedAdmission.Examples
open NativeFamilyWire

/-- A checked heap data family, followed by an owned constructor global. -/
private def snapshot : Snapshot :=
  ⟨[⟨0, 5⟩], [⟨true, 0, 0, 0, [3]⟩],
    #[.node (.ind 0 0) [], .node (.natural 2) [], .node .buffer [1],
      .node (.pi false) [2, 0], .node (.integer 0) [],
      .node (.con 0 0 1) [6], .node .alloc [1, 4]]⟩

/-- Version-6 arenas must be backward: use a separate ordered graph. -/
private def acceptedSnapshot : Snapshot :=
  ⟨[⟨0, 6⟩], [⟨true, 0, 0, 0, [3]⟩],
    #[.node (.ind 0 0) [], .node (.natural 2) [], .node .buffer [1],
      .node (.pi false) [2, 0], .node (.integer 0) [],
      .node .alloc [1, 4], .node (.con 0 0 1) [5]]⟩

theorem exact_owned_constructor_program :
    checkBytes 40 40 (encodeSnapshot acceptedSnapshot) = true := by
  rw [checkBytes_encode]
  cbv

theorem exact_source_history_and_invariants :
    ∃ definitions families env, decodeProgram acceptedSnapshot = some (definitions, families) ∧
      UnifiedProgram.UnifiedProgramChecked definitions (families.map declaration) env ∧
      UnifiedProgram.EnvWellFormed env :=
  checkSnapshot_sound (by cbv : checkSnapshot 40 40 acceptedSnapshot = true)

theorem forward_graph_reference_rejected : checkBytes 40 40 (encodeSnapshot snapshot) = false := by
  rw [checkBytes_encode]
  cbv

theorem forged_family_arity_rejected : checkBytes 40 40 (encodeSnapshot
    { acceptedSnapshot with families := [⟨true, 0, 1, 0, [3]⟩] }) = false := by
  rw [checkBytes_encode]
  cbv

end Jihoo.NativeKernel.NativeUnifiedAdmission.Examples
