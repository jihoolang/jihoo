import Jihoo.NativeContextQuantityOrigins
import Jihoo.NativeCallReplayExtension
import Jihoo.NativeKindPrefixInterpretation

/-! Connect the executable projection's call guard to authenticated closing
interpretations. The checker traces are retained at their original prefix;
no executable completeness or arbitrary code substitution is assumed. -/
namespace Jihoo.NativeKernel.Environment.ContextQuantity
open CodeKinds CallReplay
open Jihoo.Quantity
variable {control : Control}
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem app_interpreted_result
    (projected : projectRaw (fuel + 1) before ctx (.app function argument) = some control)
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (closing : Interpretation after ctx values) :
    ∃ head supplied entries result signature,
      NativeQuantity.splitSpine fuel (.app function argument) [] = some (head,supplied) ∧
      ContextFormed before ctx ∧
      SignatureTrace after ctx false signature supplied entries result ∧
      HasType after ctx false (applications head supplied) result ∧
      (entries.any (ownsArgument before) = false ∨ PiSeparated after (result.subst values)) := by
  obtain ⟨head,supplied,entries,result,signature,split,formed,typed,steps,applied,guarded⟩ :=
    app_authenticated projected
  refine ⟨head,supplied,entries,result,signature,split,formed,
    steps.signatureTrace.extend extension,applied.extend extension,?_⟩
  rcases guarded with noOwner | represented
  · exact Or.inl noOwner
  · exact Or.inr (represented.closed_nonFunction_in_extension extension history closing)

end Jihoo.NativeKernel.Environment.ContextQuantity
