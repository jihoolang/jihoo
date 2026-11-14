import Jihoo.NativeCallReplay
import Jihoo.NativeEnvironmentPlainSeparation
import Jihoo.NativeEnvironmentWellFormed

/-! Representation facts for actual code kind arguments. These certificates
retain the executable application check; no interpretation is narrowed to
literal indices or syntactic lambda values. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds

/-- A closed interpretation is an actual checked code argument at this kind.
The executable application gate, including normalization, is recomputed. -/
def Admitted (env : Environment) (kind : Kind) (value : Term) : Prop :=
  ∃ fuel, Checker.check fuel env [] false value kind.term = true ∧
    Checker.applicationOK fuel env false kind.term value = true

theorem Admitted.typed (admitted : Admitted env kind value) :
    HasType env [] false value kind.term := by
  obtain ⟨_, checked, _⟩ := admitted
  exact Checker.check_sound checked

theorem Admitted.normal_plain (admitted : Admitted env kind value) :
    ∃ normal, Conversion.Conv env value normal ∧ plain env normal = true := by
  obtain ⟨_, _, checked⟩ := admitted
  exact CallReplay.kindArgument_plain checked

theorem Admitted.not_buffer (wf : UnifiedProgram.EnvWellFormed env) (admitted : Admitted env kind value) :
    ¬ Conversion.Conv env value (.buffer n) := by
  obtain ⟨normal, normalized, isPlain⟩ := admitted.normal_plain
  intro converted
  exact plain_not_buffer_delta wf.admissible isPlain (.trans (.symm normalized) converted)

theorem Admitted.not_ref (wf : UnifiedProgram.EnvWellFormed env) (admitted : Admitted env kind value) :
    ¬ Conversion.Conv env value (.ref owner) := by
  obtain ⟨normal, normalized, isPlain⟩ := admitted.normal_plain
  intro converted
  exact plain_not_ref_delta wf.admissible isPlain (.trans (.symm normalized) converted)

theorem Admitted.nonFunction (wf : UnifiedProgram.EnvWellFormed env) (admitted : Admitted env kind value) : PiSeparated env value := by
  obtain ⟨normal, normalized, isPlain⟩ := admitted.normal_plain
  intro erased domain body converted
  exact plain_not_pi_delta wf.admissible isPlain (.trans (.symm normalized) converted)

theorem Admitted.not_back (wf : UnifiedProgram.EnvWellFormed env) (admitted : Admitted env kind value) :
    ¬ Conversion.Conv env value (.back erased owner motive) := by
  obtain ⟨normal, normalized, isPlain⟩ := admitted.normal_plain
  intro converted
  exact plain_not_back_delta wf.admissible isPlain (.trans (.symm normalized) converted)

theorem Admitted.not_owned (wf : UnifiedProgram.EnvWellFormed env) (admitted : Admitted env kind value) : ¬ Owned env value := by
  intro owned
  cases owned with
  | buffer converted => exact admitted.not_buffer wf converted
  | family found boxed converted =>
      obtain ⟨normal, normalized, isPlain⟩ := admitted.normal_plain
      exact plain_not_boxed_family_delta wf.admissible isPlain found boxed (.trans (.symm normalized) converted)

end Jihoo.NativeKernel.Environment.CodeKinds
