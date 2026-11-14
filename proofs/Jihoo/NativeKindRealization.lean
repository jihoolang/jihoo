import Jihoo.NativeKindInterpretation
import Jihoo.NativePlainIndexSeparation

/-! Every actual admitted first-order type/family argument realizes its kind.
Realizations admit arbitrary checked neutral/computed values and arbitrary
U64 index expressions. They do not require literal index canonicity. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}
open Representation

structure Realizes (env : Environment) (kind : Kind) (value : Term) : Prop where
  typed : HasType env [] true value kind.term
  representation : ∃ normal, EnvironmentDelta.Forward env value normal ∧ PlainIndices env [] normal

private theorem normalize_forward (env : Environment) (fuel : Nat) (term : Term) :
    EnvironmentDelta.Forward env term (Conversion.normalize env fuel term) := by
  change EnvironmentDelta.Forward env term ((Conversion.normalize? env fuel term).getD term)
  cases found : Conversion.normalize? env fuel term with
  | none => exact .refl
  | some normal => exact Conversion.normalize?_forward found

theorem Admitted.realizes (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (admitted : Admitted env kind value) : Realizes env kind value := by
  obtain ⟨fuel, checked, application⟩ := admitted
  have typed := (Checker.check_sound checked).ghost
  have forward := normalize_forward env fuel value
  have normalized := typed.ghostForward history forward
  have isPlain := CallReplay.kindArgument_normal_plain application
  exact ⟨typed,_,forward,PlainIndices.of_familyPlain normalized.term_wellFormed
    (plain_familyPlain isPlain) (Bool.and_eq_true_iff.mp isPlain).1⟩

theorem Realizes.index {index : Term}
    (realized : Realizes env (.index erased rest) function)
    (argument : HasType env [] true index .u64) : Realizes env rest (.app function index) := by
  obtain ⟨normal, forward, plain⟩ := realized.representation
  have typed : HasType env [] true (.app function index) rest.term := by
    simpa only [Kind.term, Bool.true_or, Kind.subst] using
      HasType.app realized.typed argument (Or.inl rfl)
  exact ⟨typed, .app normal index,
    .node .app (.cons forward (.cons .refl .nil)), plain.u64_application argument⟩

theorem Realizes.not_owned (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (realized : Realizes env kind value) : ¬ Owned env value := by
  obtain ⟨normal, forward, plain⟩ := realized.representation
  intro owned
  exact plain.not_owned history (realized.typed.ghostForward history forward) (owned.congr (EnvironmentDelta.Basis.forward_toConv forward))

theorem Realizes.nonFunction (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (realized : Realizes env kind value) : PiSeparated env value := by
  obtain ⟨normal, forward, plain⟩ := realized.representation
  intro erased domain body converted
  exact plain.nonFunction history (realized.typed.ghostForward history forward) erased domain body
    (.trans (.symm (EnvironmentDelta.Basis.forward_toConv forward)) converted)

theorem Realizes.not_ref (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (realized : Realizes env kind value) : ¬ Conversion.Conv env value (.ref owner) := by
  obtain ⟨normal, forward, plain⟩ := realized.representation
  intro converted
  exact plain.not_ref history (realized.typed.ghostForward history forward)
    (.trans (.symm (EnvironmentDelta.Basis.forward_toConv forward)) converted)

theorem Realizes.not_back (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (realized : Realizes env kind value) : ¬ Conversion.Conv env value (.back erased owner motive) := by
  obtain ⟨normal, forward, plain⟩ := realized.representation
  intro converted
  exact plain.not_back history (realized.typed.ghostForward history forward)
    (.trans (.symm (EnvironmentDelta.Basis.forward_toConv forward)) converted)

end Jihoo.NativeKernel.Environment.CodeKinds
