import Jihoo.NativeDefinitions

/-! Declaration modes are derived from sorts, including on synthetic inputs
which an actual native program checker would reject before exporting. -/
namespace Jihoo.NativeKernel.Definitions.Examples

private def erasedData : Definition :=
  ⟨.pi true .u64 .u64, .lam true .u64 (.var 0)⟩

private def erasedProof : Definition :=
  ⟨.pi true .u64 (.eq (.var 0) (.var 0)), .lam true .u64 (.refl (.var 0))⟩

theorem data_ghost_observation :
    Checker.check 16 [] true erasedData.value erasedData.type = true := by cbv

theorem data_declaration_rejected : check 16 erasedData = false := by cbv

theorem erased_index_proof_declaration : check 16 erasedProof = true := by cbv

theorem scalar_declaration : check 8 ⟨.u64, .natural 7⟩ = true := by cbv

theorem type_declaration : check 8 ⟨.univ 1, .univ 0⟩ = true := by cbv

theorem type_in_type_rejected : check 8 ⟨.univ 0, .univ 0⟩ = false := by cbv

private def erasedDataSnapshot : NativeWire.Snapshot :=
  ⟨true, 2, 3, #[.node .u64 [], .var 0, .node (.lam true) [0, 1],
    .node (.pi true) [0, 0]]⟩

theorem ghost_snapshot_observation : NativeAdmission.checkSnapshot 16 erasedDataSnapshot = true := by cbv

theorem forged_ghost_mode_cannot_authorize_code :
    checkSnapshot 16 erasedDataSnapshot = false := by cbv

theorem declaration_ignores_claimed_mode (mode : Bool) :
    checkSnapshot 16 { erasedDataSnapshot with ghost := mode } = false := by
  rw [checkSnapshot_mode]
  exact forged_ghost_mode_cannot_authorize_code

end Jihoo.NativeKernel.Definitions.Examples
