import Jihoo.NativeProgramAdmission

namespace Jihoo.NativeKernel.NativeProgramAdmission.Examples

open NativeProgramWire

private def chain : Snapshot := ⟨[⟨0, 1⟩, ⟨0, 2⟩],
  #[.node .u64 [], .node (.natural 7) [], .node (.global 0) []]⟩

theorem exact_global_chain_accepted : checkBytes 32 (encodeSnapshot chain) = true := by
  rw [checkBytes_encode]
  cbv

theorem exact_global_chain_sound : Sound chain :=
  checkSnapshot_sound (by cbv : checkSnapshot 32 chain = true)

private def typeAlias : Snapshot := ⟨[⟨0, 1⟩, ⟨2, 3⟩],
  #[.node (.universe 0) [], .node .u64 [], .node (.global 0) [], .node (.natural 7) []]⟩

theorem type_alias_body_mode_computed : checkBytes 32 (encodeSnapshot typeAlias) = true := by
  rw [checkBytes_encode]
  cbv

theorem self_reference_rejected : checkBytes 32 (encodeSnapshot
    ⟨[⟨0, 2⟩], chain.arena⟩) = false := by
  rw [checkBytes_encode]
  cbv

theorem forward_reference_rejected : checkBytes 32 (encodeSnapshot
    ⟨[⟨0, 2⟩, ⟨0, 1⟩], #[.node .u64 [], .node (.natural 7) [], .node (.global 1) []]⟩) = false := by
  rw [checkBytes_encode]
  cbv

theorem arbitrary_missing_global_rejected : checkBytes 32 (encodeSnapshot
    ⟨[⟨0, 2⟩], #[.node .u64 [], .node (.natural 7) [], .node (.global 99) []]⟩) = false := by
  rw [checkBytes_encode]
  cbv

theorem forged_erased_runtime_value_rejected : checkBytes 32 (encodeSnapshot
    ⟨[⟨2, 3⟩], #[.node .u64 [], .var 0, .node (.pi true) [0, 0],
      .node (.lam true) [0, 1]]⟩) = false := by
  rw [checkBytes_encode]
  cbv

theorem unused_bad_graph_rejected : checkBytes 32 (encodeSnapshot
    ⟨[⟨0, 1⟩], chain.arena.push (.node .uadd [3, 3])⟩) = false := by
  rw [checkBytes_encode]
  cbv

theorem empty_program_accepted : checkBytes 32 (encodeSnapshot ⟨[], #[]⟩) = true := by
  rw [checkBytes_encode]
  cbv

end Jihoo.NativeKernel.NativeProgramAdmission.Examples
