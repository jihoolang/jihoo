import Jihoo.NativeAdmission

/-! End-to-end exact-envelope examples for universes, erased indices, mode
safety, complete-graph validation and canonical transport. -/
namespace Jihoo.NativeKernel.NativeAdmission.Examples
open NativeWire NativeArena

private def sortSnapshot : Snapshot :=
  ⟨true, 0, 1, #[.node (.universe 0) [], .node (.universe 1) []]⟩

private def erasedIndex : Snapshot :=
  ⟨false, 3, 5, #[.node .u64 [], .var 0, .node .refl [1],
    .node (.lam true) [0, 2], .node .eq [1, 1], .node (.pi true) [0, 4]]⟩

private def erasedIdentity : Snapshot :=
  ⟨true, 2, 3, #[.node .u64 [], .var 0, .node (.lam true) [0, 1],
    .node (.pi true) [0, 0]]⟩

theorem universe_snapshot : checkSnapshot 12 sortSnapshot = true := by cbv

theorem universe_bytes : checkBytes 12 (encodeSnapshot sortSnapshot) = true := by
  rw [checkBytes_encode]
  exact universe_snapshot

theorem erased_index : checkSnapshot 16 erasedIndex = true := by cbv

theorem ghost_erased_available : checkSnapshot 12 erasedIdentity = true := by cbv

theorem runtime_erased_rejected :
    checkSnapshot 12 { erasedIdentity with ghost := false } = false := by cbv

theorem unused_cycle : checkSnapshot 12 { sortSnapshot with
    arena := sortSnapshot.arena.push (.node .array [2]) } = false := by cbv

theorem malformed_arity : checkSnapshot 12 { sortSnapshot with
    arena := sortSnapshot.arena.push (.node (.elements 3) [0, 1]) } = false := by cbv

theorem false_equality : checkSnapshot 12
    ⟨true, 1, 3, #[.node (.natural 0) [], .node .refl [0],
      .node (.natural 1) [], .node .eq [0, 2]]⟩ = false := by cbv

theorem universe_payload_limit : checkSnapshot 12 { sortSnapshot with
    arena := sortSnapshot.arena.push (.node (.universe 33) []) } = false := by cbv

theorem trailing_byte :
    checkBytes 12 (encodeSnapshot sortSnapshot ++ ByteArray.mk #[10]) = false := by
  simp [checkBytes, decodeSnapshot, encodeSnapshot, parseSnapshot_encode]

theorem zero_fuel : checkSnapshot 0 sortSnapshot = false := by cbv

end Jihoo.NativeKernel.NativeAdmission.Examples
