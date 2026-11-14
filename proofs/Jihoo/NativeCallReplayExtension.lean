import Jihoo.NativeCallReplay
import Jihoo.NativeEnvironmentExtension

/-! Stable replay retains successful executable traces at their authentic
origin extension. Bounded environment-dependent checking is not assumed complete
or monotone when rerun in a larger environment. -/
namespace Jihoo.NativeKernel.Environment.CallReplay

/-- The displayed Pi was actually emitted by the bounded normalizer. -/
def NormalizedPi (env : Environment) (signature : Term) (erased : Bool) (domain codomain : Term) : Prop :=
  ∃ origin fuel, Extends origin env ∧
    Conversion.normalize? origin fuel signature = some (.pi erased domain codomain)

theorem NormalizedPi.current
    (accepted : Conversion.normalize? env fuel signature = some (.pi erased domain codomain)) :
    NormalizedPi env signature erased domain codomain := ⟨env,fuel,Extends.refl _,accepted⟩

theorem NormalizedPi.converted (trace : NormalizedPi env signature erased domain codomain) :
    Conversion.Conv env signature (.pi erased domain codomain) := by
  obtain ⟨origin,fuel,extension,accepted⟩ := trace
  exact (Conversion.normalize?_sound accepted).extend extension

theorem NormalizedPi.extend (extension : Extends before after)
    (trace : NormalizedPi before signature erased domain codomain) :
    NormalizedPi after signature erased domain codomain := by
  obtain ⟨origin,fuel,prior,accepted⟩ := trace
  exact ⟨origin,fuel,prior.trans extension,accepted⟩

/-- The native code-kind policy was actually checked; no plainness flag or
arbitrary conversion representative is a constructor. -/
def ApplicationEvidence (env : Environment) (ghost : Bool) (domain argument : Term) : Prop :=
  ∃ origin fuel, Extends origin env ∧ Checker.applicationOK fuel origin ghost domain argument = true

theorem ApplicationEvidence.current
    (accepted : Checker.applicationOK fuel env ghost domain argument = true) :
    ApplicationEvidence env ghost domain argument := ⟨env,fuel,Extends.refl _,accepted⟩

theorem ApplicationEvidence.allowed (trace : ApplicationEvidence env ghost domain argument) :
    applicationAllowed env ghost domain argument := by
  obtain ⟨origin,fuel,extension,accepted⟩ := trace
  exact applicationAllowed.extend extension (Checker.applicationOK_sound accepted)

theorem ApplicationEvidence.extend (extension : Extends before after)
    (trace : ApplicationEvidence before ghost domain argument) :
    ApplicationEvidence after ghost domain argument := by
  obtain ⟨origin,fuel,prior,accepted⟩ := trace
  exact ⟨origin,fuel,prior.trans extension,accepted⟩

inductive SignatureTrace (env : Environment) (ctx : Context) (ghost : Bool) :
    Term → List Term → List Argument → Term → Prop where
  | nil : SignatureTrace env ctx ghost signature [] [] signature
  | cons : NormalizedPi env signature erased domain codomain →
      HasType env ctx (ghost || erased) argument domain → ApplicationEvidence env ghost domain argument →
      Conversion.substitutionSafe codomain argument = true →
      SignatureTrace env ctx ghost (codomain.subst (fun | 0 => argument | n + 1 => .var n)) rest entries result →
      SignatureTrace env ctx ghost signature (argument :: rest) (⟨erased,domain,argument⟩ :: entries) result

theorem Steps.signatureTrace (checked : Steps env ctx ghost signature arguments entries result) :
    SignatureTrace env ctx ghost signature arguments entries result := by
  induction checked with
  | nil => exact .nil
  | cons normalized checked allowed safe rest ih =>
      exact .cons (.current normalized) (Checker.check_sound checked) (.current allowed) safe ih

theorem SignatureTrace.extend (extension : Extends before after)
    (checked : SignatureTrace before ctx ghost signature arguments entries result) :
    SignatureTrace after ctx ghost signature arguments entries result := by
  induction checked with
  | nil => exact .nil
  | cons normalized typed allowed safe rest ih =>
      exact .cons (normalized.extend extension) (typed.extend extension) (allowed.extend extension) safe ih

theorem SignatureTrace.apply (trace : SignatureTrace env ctx ghost signature arguments entries result)
    (typed : HasType env ctx ghost head signature) :
    HasType env ctx ghost (applications head arguments) result := by
  induction trace generalizing head with
  | nil => exact typed
  | cons normalized argument allowed _ rest ih =>
      exact ih (.app (.convert typed normalized.converted) argument allowed.allowed)

end Jihoo.NativeKernel.Environment.CallReplay
