import Jihoo.CommonDataEnvironmentCompaction

namespace Jihoo.CommonDataEnvironmentCompactionChecks
open RecursiveLexicalFields CommonDataEnvironmentCompaction

/-- CommonData keeps Data; Core removes Data and ghost, retaining real Nat and
Buffer values in order. The two lexical masks intentionally differ. -/
theorem mixed_square :
    CommonDataErasure.Env [true, false, true, true]
      [.data none, .ghost, .nat 4, .buffer 7] [.data none, .nat 4, .buffer 7] ∧
    coreMask [.data none, .ghost, .nat 4, .buffer 7] = [false, false, true, true] ∧
    coreMask [.data none, .nat 4, .buffer 7] = [false, true, true] ∧
    coreEnv [.data none, .ghost, .nat 4, .buffer 7] = [.nat 4, .owner 7] := by
  exact ⟨.keep (.erase (.keep (.keep .nil))), rfl, rfl, rfl⟩

theorem mixed_indices :
    CommonDataErasure.position [true, false, true, true] 2 = some 1 ∧
    CommonDataErasure.position [true, false, true, true] 3 = some 2 ∧
    SizedErasure.rank (coreMask [.data none, .ghost, .nat 4, .buffer 7]) 2 = 0 ∧
    SizedErasure.rank (coreMask [.data none, .nat 4, .buffer 7]) 2 = 1 := by decide

/-- Neither dead typing entries nor an empty capability inventory licenses
runtime removal of a Buffer alias. Data aliases still project to ghost. -/
theorem stale_owner_alias :
    Agrees [] [.dead, .dead, .scalar] [.data (some 99), .buffer 7, .scalar 3] ∧
    coreMask [.data (some 99), .buffer 7, .scalar 3] = [false, true, true] ∧
    coreEnv [.data (some 99), .buffer 7, .scalar 3] = [.owner 7, .scalar 3] := by
  exact ⟨.cons trivial (.cons trivial (.cons ⟨3, rfl⟩ .nil)), rfl, rfl⟩

theorem case_two_fields :
    coreMask (bindValues 0 ⟨some 11, some 12⟩ [.buffer 7, .scalar 3]) =
      [false, false, true, true] ∧
    coreEnv (bindValues 0 ⟨some 11, some 12⟩ [.buffer 7, .scalar 3]) =
      [.owner 7, .scalar 3] := ⟨rfl, rfl⟩

/-- Even an explicitly retained CommonData ghost vanishes in the Core pass. -/
theorem kept_ghost :
    CommonDataErasure.Env [true] [.ghost] [.ghost] ∧
    coreMask [.ghost] = [false] ∧ coreEnv [.ghost] = [] := ⟨.keep .nil, rfl, rfl⟩

end Jihoo.CommonDataEnvironmentCompactionChecks

#print axioms Jihoo.CommonDataEnvironmentCompaction.core_related

#print axioms Jihoo.CommonDataEnvironmentCompaction.project_compact

#print axioms Jihoo.CommonDataEnvironmentCompaction.envRel_canonical

#print axioms Jihoo.CommonDataEnvironmentCompaction.relational_square

#print axioms Jihoo.CommonDataEnvironmentCompaction.position_exists

#print axioms Jihoo.CommonDataEnvironmentCompaction.position_rank

#print axioms Jihoo.CommonDataEnvironmentCompaction.position_mask

#print axioms Jihoo.CommonDataEnvironmentCompaction.relational_position_rank

#print axioms Jihoo.CommonDataEnvironmentCompaction.select_lookup

#print axioms Jihoo.CommonDataEnvironmentCompaction.select_mask

#print axioms Jihoo.CommonDataEnvironmentCompaction.support_select

#print axioms Jihoo.CommonDataEnvironmentCompaction.lookup

#print axioms Jihoo.CommonDataEnvironmentCompaction.nat_lookup

#print axioms Jihoo.CommonDataEnvironmentCompaction.scalar_lookup

#print axioms Jihoo.CommonDataEnvironmentCompaction.buffer_lookup

#print axioms Jihoo.CommonDataEnvironmentCompaction.data_erased

#print axioms Jihoo.CommonDataEnvironmentCompaction.ghost_erased

#print axioms Jihoo.CommonDataEnvironmentCompaction.buffer_retained

#print axioms Jihoo.CommonDataEnvironmentCompaction.nat_binder

#print axioms Jihoo.CommonDataEnvironmentCompaction.scalar_binder

#print axioms Jihoo.CommonDataEnvironmentCompaction.owner_binder

#print axioms Jihoo.CommonDataEnvironmentCompaction.data_binder

#print axioms Jihoo.CommonDataEnvironmentCompaction.case_binders

#print axioms Jihoo.CommonDataEnvironmentCompaction.case_position_rank

#print axioms Jihoo.CommonDataEnvironmentCompaction.projected_support

#print axioms Jihoo.CommonDataEnvironmentCompaction.projected_support_compacted

#print axioms Jihoo.CommonDataEnvironmentCompaction.common_mask_not_core

#print axioms Jihoo.CommonDataEnvironmentCompaction.data_buffer_counterexample

#print axioms Jihoo.CommonDataEnvironmentCompactionChecks.mixed_square

#print axioms Jihoo.CommonDataEnvironmentCompactionChecks.mixed_indices

#print axioms Jihoo.CommonDataEnvironmentCompactionChecks.stale_owner_alias

#print axioms Jihoo.CommonDataEnvironmentCompactionChecks.case_two_fields

#print axioms Jihoo.CommonDataEnvironmentCompactionChecks.kept_ghost
