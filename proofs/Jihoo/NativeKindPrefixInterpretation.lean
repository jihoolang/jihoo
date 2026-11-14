import Jihoo.NativeCodeInterpretation
import Jihoo.NativeEnvironmentExtension
import Jihoo.NativeCallReplay

/-! Old checked functions may receive later admissible type/family arguments.
The source kind spine transports through actual typed lookup and argument
judgments; executable checker completeness is never assumed. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

inductive SemanticSpine (env : Environment) (ctx : Context) : Term → Kind → Prop where
  | var : LookupKind env ctx index kind → SemanticSpine env ctx (.var index) kind
  | app : SemanticSpine env ctx function (.index erased result) →
      HasType env ctx true argument .u64 → SemanticSpine env ctx (.app function argument) result

theorem Spine.semantic (source : Spine env ctx term kind) : SemanticSpine env ctx term kind := by
  induction source with
  | var found => exact .var found
  | app head checked ih => exact .app ih (Checker.check_sound checked)

theorem SemanticSpine.extend (extension : Extends before after)
    (source : SemanticSpine before ctx term kind) : SemanticSpine after ctx term kind := by
  induction source with
  | var found =>
      obtain ⟨binding,selected,converted,typed⟩ := found
      exact .var ⟨binding,selected,converted.extend extension,typed.extend extension⟩
  | app head typed ih => exact .app ih (typed.extend extension)

theorem SemanticSpine.realizes (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (source : SemanticSpine env ctx term kind) (closing : Interpretation env ctx values) :
    Realizes env kind (term.subst values) := by
  induction source with
  | @var index kind found =>
      simpa only [Term.subst] using (closing.arguments index kind found).realizes history
  | @app function erased result argument head typed ih =>
      have closedIndex : HasType env [] true (argument.subst values) .u64 := by
        simpa only [Term.subst,substArgs] using typed.ghostSubstitution history.wellFormed closing.typed
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using ih.index closedIndex

theorem Spine.realizes_in_extension (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after) (source : Spine before ctx term kind)
    (closing : Interpretation after ctx values) : Realizes after kind (term.subst values) :=
  (source.semantic.extend extension).realizes history closing

theorem abstractDomain_not_owned_in_extension (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after) (normalized : Conversion.Conv before domain normal)
    (source : Spine before ctx normal (.type level)) (closing : Interpretation after ctx values) :
    ¬ Owned after (domain.subst values) := by
  intro owned
  exact (source.realizes_in_extension extension history closing).not_owned history
    (owned.congr ((normalized.extend extension).substitution values history.wellFormed.closed))

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.CallReplay
open CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

/-- The owner-consuming call guard remains valid under admissible code closure,
including abstract results F i with arbitrary typed U64 indices. -/
theorem ResultShape.closed_nonFunction_in_extension
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (shape : ResultShape before ctx result)
    (closing : Interpretation after ctx values) : PiSeparated after (result.subst values) := by
  cases shape with
  | @rigid op children converted head =>
      have reduced := (converted.extend extension).substitution values history.wellFormed.closed
      have witnessed : nonFunction after (result.subst values) := by
        apply EnvironmentDelta.Basis.NonFunction.of_conversion reduced
        apply EnvironmentDelta.Basis.NonFunction.ofHead
        simpa only [Term.subst,EnvironmentDelta.Basis.nonFunctionHead] using head
      intro erased domain body pi
      exact witnessed.not_pi pi history.wellFormed.admissible
  | abstract converted spine =>
      have abstracted := (spine.realizes_in_extension extension history closing).nonFunction history
      intro erased domain body pi
      exact abstracted erased domain body
        (.trans (.symm ((converted.extend extension).substitution values history.wellFormed.closed)) pi)

theorem ResultShape.closed_nonFunction
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (shape : ResultShape env ctx result) (closing : Interpretation env ctx values) :
    PiSeparated env (result.subst values) :=
  shape.closed_nonFunction_in_extension (Extends.refl _) history closing

end Jihoo.NativeKernel.Environment.CallReplay
