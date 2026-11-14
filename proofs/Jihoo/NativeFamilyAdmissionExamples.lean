import Jihoo.NativeFamilyAdmission

namespace Jihoo.NativeKernel.NativeFamilyAdmission.Examples

open NativeFamilyWire

private def natGraph : NativeArena.Arena :=
  #[.node (.ind 0 0) [], .node (.pi false) [0, 0]]
private def natSnapshot : Snapshot := ⟨[], [⟨true, 0, 0, 0, [0, 1]⟩], natGraph⟩

theorem exact_recursive_data_signature_accepted :
    checkBytes 32 (encodeSnapshot natSnapshot) = true := by
  rw [checkBytes_encode]
  cbv

theorem recursive_data_admission_sound : Sound natSnapshot :=
  checkSnapshot_sound (by cbv : checkSnapshot 32 natSnapshot = true)

theorem exact_proposition_signature_accepted : checkBytes 32
    (encodeSnapshot ⟨[], [⟨false, 0, 0, 0, [0]⟩], #[.node (.ind 0 0) []]⟩) = true := by
  rw [checkBytes_encode]
  cbv

theorem raw_negative_recursion_rejected : checkBytes 32 (encodeSnapshot
    ⟨[], [⟨true, 0, 0, 0, [3]⟩], #[.node (.ind 0 0) [], .node .u64 [],
      .node (.pi false) [0, 1], .node (.pi false) [2, 0]]⟩) = false := by
  rw [checkBytes_encode]
  cbv

theorem relevant_recursive_proposition_field_rejected : checkBytes 32
    (encodeSnapshot ⟨[], [⟨false, 0, 0, 0, [1]⟩], natGraph⟩) = false := by
  rw [checkBytes_encode]
  cbv

theorem erased_recursive_data_field_rejected : checkBytes 32 (encodeSnapshot
    ⟨[], [⟨true, 0, 0, 0, [1]⟩], #[.node (.ind 0 0) [], .node (.pi true) [0, 0]]⟩) = false := by
  rw [checkBytes_encode]
  cbv

theorem out_of_order_family_rejected : checkBytes 32
    (encodeSnapshot ⟨[], [⟨true, 0, 0, 1, [0]⟩], natGraph⟩) = false := by
  rw [checkBytes_encode]
  cbv

theorem externally_forged_arity_rejected : checkBytes 32
    (encodeSnapshot ⟨[], [⟨true, 0, 17, 0, [0]⟩], natGraph⟩) = false := by
  rw [checkBytes_encode]
  cbv

end Jihoo.NativeKernel.NativeFamilyAdmission.Examples
