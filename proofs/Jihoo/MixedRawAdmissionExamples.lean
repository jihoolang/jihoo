import Jihoo.MixedRawAdmission
set_option maxRecDepth 4096

namespace Jihoo.CoreBridge.Checked.Admission
open GraphCertificates

def literalSnapshot : Typing.Wire.Snapshot :=
  ⟨1, 2, #[.natural 7, .refl 0, .eq 0 0]⟩

theorem literal_accepted : (admitSnapshot literalSnapshot).isSome = true := by decide +kernel

theorem false_type_rejected :
    (admit (.refl (.natural 7)) (.eq (.natural 7) (.natural 8))).isSome = false := by decide +kernel

theorem erased_natural_rejected :
    (admit (.lam true .u64 (.refl (.var 0)))
      (.pi true .u64 (.eq (.var 0) (.var 0)))).isSome = false := by decide +kernel

theorem proof_namespace_recovered :
    position .value 2 [.value, .index, .value, .index] = some 1 ∧
    position .index 2 [.value, .index, .value, .index] = none := by decide +kernel

theorem non_atomic_application_rejected :
    (admit (.app (.lam false .u64 (.refl (.var 0))) (.uadd (.natural 1) (.natural 1)))
      (.eq (.natural 2) (.natural 2))).isSome = false := by decide +kernel

theorem unreachable_invalid_rejected :
    (admitSnapshot ⟨1, 2, #[.natural 7, .refl 0, .eq 0 0, .array 3]⟩).isSome = false := by decide +kernel

theorem separate_tree_budget : cost 33 (.elements (List.replicate 512 (.integer 0))) = 513 := by decide +kernel

end Jihoo.CoreBridge.Checked.Admission
