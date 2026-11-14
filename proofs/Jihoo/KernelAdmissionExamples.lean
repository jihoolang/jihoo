import Jihoo.KernelAdmission

/-! Concrete graph and canonical-byte acceptance, without a derivation
certificate. The accepted program returns equality evidence from a dependent
application; mutations preserve that program while changing its envelope. -/
namespace Jihoo.KernelAdmission.Examples

open GraphCertificates GraphCertificates.Typing.Wire

private def dependent : Snapshot :=
  { graph := #[.u64, .var 0, .refl 1, .lam false 0 2,
      .natural 7, .app 3 4, .eq 4 4]
    termRoot := 5
    typeRoot := 6 }

theorem dependent_snapshot : checkSnapshot 12 dependent = true := by cbv

theorem dependent_bytes : checkBytes 12 (encodeSnapshot dependent) = true := by
  rw [checkBytes_encode]
  exact dependent_snapshot

theorem false_equality :
    checkSnapshot 12 { dependent with
      graph := dependent.graph ++ #[.natural 8, .eq 4 7]
      typeRoot := 8 } = false := by cbv

theorem type_as_term :
    checkSnapshot 12 { dependent with termRoot := 0 } = false := by cbv

theorem invalid_root :
    checkSnapshot 12 { dependent with typeRoot := 99 } = false := by cbv

theorem unused_cycle :
    checkSnapshot 12 { dependent with
      graph := dependent.graph.push (.array 7) } = false := by cbv

theorem trailing_byte :
    checkBytes 12 (encodeSnapshot dependent ++ ByteArray.mk #[10]) = false := by cbv

theorem zero_fuel : checkSnapshot 0 dependent = false := by cbv

end Jihoo.KernelAdmission.Examples
