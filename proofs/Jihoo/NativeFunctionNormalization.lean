import Jihoo.NativeFunctionFundamental
import Jihoo.NativeNumeralForward
import Jihoo.NativeEnvironmentContextualPreservation

/-! Actual finite forward normalization for the recognized U64/function source
fragment. Full ACU reduction is not strongly normalizing: commutativity cycles.
These theorems assert reachability and unique numeral results, without assuming
success of a bounded implementation or supplying source realization evidence. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Functions

theorem Expression.closed_natural_forward (wf : UnifiedProgram.EnvWellFormed env)
    (expression : Expression [] .natural) :
    EnvironmentDelta.Forward env expression.syntax (.natural (expression.meaning .nil)) :=
  EnvironmentDelta.NumeralForward.conversion_to_forward wf.admissible
    (expression.closed_natural_conversion (env := env)).2 (expression.closed_natural_conversion (env := env)).1

theorem closed_native_natural_forward (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env [] mode term .u64) (recognized : Recognized term) :
    ∃ value, value < 2^64 ∧ EnvironmentDelta.Forward env term (.natural value) := by
  obtain ⟨value,bound,converted⟩ := closed_natural_canonicity wf typed recognized
  exact ⟨value,bound,EnvironmentDelta.NumeralForward.conversion_to_forward wf.admissible converted bound⟩

theorem forward_numeral_unique (wf : UnifiedProgram.EnvWellFormed env)
    (first : EnvironmentDelta.Forward env term (.natural left))
    (second : EnvironmentDelta.Forward env term (.natural right)) : left = right :=
  ((EnvironmentDelta.Basis.forward_toConv first).symm.trans
    (EnvironmentDelta.Basis.forward_toConv second)).natural_injective wf.admissible

/-- The original source type may retain a global alias or an unformed raw
conversion representative. Checked history supplies genuine delta preservation. -/
theorem checked_original_type_normalization
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env [] mode term type) (recognized : Recognized term)
    (naturalType : Conversion.Conv env type .u64) :
    ∃ value, value < 2^64 ∧ EnvironmentDelta.Forward env term (.natural value) ∧
      HasType env [] true (.natural value) type ∧
      ∀ other, EnvironmentDelta.Forward env term (.natural other) → other = value := by
  obtain ⟨value,bound,path⟩ := closed_native_natural_forward history.wellFormed
    (typed.convert naturalType) recognized
  exact ⟨value,bound,path,typed.ghostForward history path,
    fun _ otherPath => forward_numeral_unique history.wellFormed otherPath path⟩

namespace NormalizationExamples
private theorem emptyWellFormed : UnifiedProgram.EnvWellFormed empty :=
  UnifiedProgram.UnifiedProgramChecked.empty.wellFormed

private def identity : Term := .lam false .u64 (.var 0)
private def source : Term := .app identity (.natural 23)

theorem checker_derived_source_reaches_a_numeral :
    ∃ value, value < 2^64 ∧ EnvironmentDelta.Forward empty source (.natural value) :=
  closed_native_natural_forward emptyWellFormed
    (Checker.infer_sound (by cbv : Checker.infer 16 empty [] false source = some .u64))
    (.app (.lam .natural .var) .natural)

/-- A machine-word-sized unary arithmetic expansion remains symbolic in this
proof: it is never allocated or evaluated by cbv/decide. -/
theorem wide_symbolic_split_rejoins : EnvironmentDelta.Forward empty
    (ACU.compact (List.replicate (2^63) (.natural 1))) (.natural (2^63)) :=
  (EnvironmentDelta.NumeralForward.replicate_ones (2^63)).contract (by decide)

private def chain : Nat → Expression [] .natural
  | 0 => .natural 23 (by decide)
  | n+1 => .app (.lam (.var .here)) (chain n)

/-- No fixed normalization depth or successful search is assumed. -/
theorem arbitrary_depth_identity_chain (depth : Nat) :
    EnvironmentDelta.Forward empty (chain depth).syntax (.natural 23) := by
  have value : ∀ depth, (chain depth).meaning .nil = 23 := by
    intro depth
    induction depth with
    | zero => rfl
    | succ depth ih => simpa only [chain,Expression.meaning,Member.value] using ih
  simpa only [value] using (chain depth).closed_natural_forward emptyWellFormed

theorem original_unformed_type_retained :
    HasType empty [] true (.natural 23) (.uadd .u64 (.natural 0)) := by
  have sourceTyped : HasType empty [] false source (.uadd .u64 (.natural 0)) :=
    (Checker.infer_sound (by cbv : Checker.infer 16 empty [] false source = some .u64)).convert
      (.acu (.symm (.zero .u64)))
  obtain ⟨value,bound,path,typed,unique⟩ := checked_original_type_normalization
    UnifiedProgram.UnifiedProgramChecked.empty sourceTyped
    (.app (.lam .natural .var) .natural) (.acu (.zero .u64))
  have beta : EnvironmentDelta.Forward empty source (.natural 23) :=
    .acu (.compute (by simpa only [source,identity,Term.subst,NativeKernel.single] using
      ACU.Computes.beta false .u64 (.var 0) (.natural 23)))
  simpa only [← unique 23 beta] using typed

end NormalizationExamples
end Jihoo.NativeKernel.Environment.Semantics.Functions
