import Jihoo.NativeEnvironmentPlainSeparation

namespace Jihoo.NativeKernel.Environment.PlainExamples

private def neutral : Term := .app (.var 0) (.natural 3)

theorem arbitrary_neutral_atom_plain : Environment.plain empty neutral = true := by cbv

theorem neutral_cannot_become_owned : ¬ Conversion.Conv neutral (.buffer (.natural 3)) :=
  plain_not_buffer arbitrary_neutral_atom_plain

theorem neutral_cannot_become_function : nonFunction neutral :=
  plain_nonFunction arbitrary_neutral_atom_plain

private def deadOwner : Term := .app (.lam false (.univ 0) .u64) (.buffer (.natural 0))

theorem reverse_beta_does_not_preserve_plain :
    Environment.plain empty .u64 = true ∧ Environment.plain empty deadOwner = false ∧
    Conversion.Conv deadOwner .u64 := by
  refine ⟨by cbv,by cbv,?_⟩
  exact .legacy (by simpa only [deadOwner,Term.subst,substArgs] using
    Jihoo.NativeKernel.Conversion.Conv.beta false (.univ 0) .u64 (.buffer (.natural 0)))

private def flat : CheckedFamily := ⟨⟨true,0,0,[],0⟩,[],false⟩
private def boxed : CheckedFamily := ⟨⟨true,0,0,[],0⟩,[],true⟩
private def env : Environment := ⟨#[],#[flat,boxed]⟩
private def flatType : Term := .node (.ind 0 0) []

theorem flat_family_plain : Environment.plain env flatType = true := by cbv

theorem flat_cannot_become_boxed : ¬ Conversion.Conv flatType (.node (.ind 1 0) []) :=
  plain_not_boxed_family flat_family_plain (by rfl) (by rfl)

theorem unresolved_alias_not_plain : Environment.plain env (.node (.global 0) []) = false := by cbv

end Jihoo.NativeKernel.Environment.PlainExamples
