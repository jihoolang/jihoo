import Jihoo.NativeAtomicSupport

/-! A concrete first-stage semantic observer on the full unified checker.
The observer checks actual source typing, runs the actual bounded normalizer,
and recognizes a proof-head fragment. It never decides the requested claim's
truth. Completeness/normalization for all typed proofs is not asserted. -/
namespace Jihoo.NativeKernel.Environment.Semantics
open Jihoo.NativeKernel.Environment.Conversion

def evidenceHead : Term → Bool
  | .refl _ | .decide _ _ => true
  | .strict _ rest | .free _ rest | .node (.drop _) [_,rest] => evidenceHead rest
  | .ifLt _ _ _ no | .ifEq _ _ _ no => evidenceHead no
  | _ => false
termination_by term => sizeOf term

/-- This is a theorem about every actual HasType derivation in the displayed
syntactic fragment, rather than an assumed realization of that derivation. -/
theorem evidenceHead_realize (typed : HasType env ctx mode term type)
    (recognized : evidenceHead term = true) : AtomicTruth env type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ term type _ => evidenceHead term = true → AtomicTruth env type)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  all_goals try (simp only [evidenceHead,Bool.false_eq_true] at *)
  case refl => exact .equality (.refl _)
  case decide => rename_i left right ordered accepted; exact .less (.refl _) (.refl _) ordered
  case decideConverted =>
    rename_i left right leftConv rightConv leftBound rightBound ordered _ _ accepted
    exact .less leftConv rightConv ordered
  case strict => rename_i left right ihleft ihright accepted; exact ihright accepted
  case free => rename_i owner rest ihowner ihrest accepted; exact ihrest accepted
  case drop => rename_i found boxed owner rest ihowner ihrest accepted; exact ihrest accepted
  case ifLt => rename_i left right yes no ihleft ihright ihyes ihno accepted; exact ihno accepted
  case ifEq => rename_i left right yes no ihleft ihright ihyes ihno accepted; exact ihno accepted
  case convert => rename_i typed converted ih accepted; exact .convert (ih accepted) converted
  case dataElim =>
    rename_i family entry analysis ctx motive proof ghost scrutinee indices types branches found isData boxed size motiveTyped scrutineeTyped generated branchTyped allowed ihm ihs ihb accepted
    cases analysis <;> simp only [↓reduceIte,evidenceHead,Bool.false_eq_true] at accepted

inductive AtomicClaim where
  | equal : Nat → Nat → AtomicClaim
  | less : Nat → Nat → AtomicClaim
  deriving Repr, DecidableEq

def AtomicClaim.type : AtomicClaim → Term
  | .equal m n => .eq (.natural m) (.natural n)
  | .less m n => .lt (.natural m) (.natural n)

def AtomicClaim.Holds : AtomicClaim → Prop
  | .equal m n => m = n
  | .less m n => m < n

theorem AtomicClaim.realized (wf : UnifiedProgram.EnvWellFormed env) {claim : AtomicClaim} (realized : AtomicTruth env claim.type) : claim.Holds := by
  cases claim with
  | equal m n => exact (AtomicTruth.equal_endpoints wf realized (.refl _)).natural_injective wf.admissible
  | less m n => exact AtomicTruth.less_numerals wf realized (.refl _)

/-- Admission checks the actual unified judgment and proof-head support only.
No branch calls decide on the arithmetic relation requested by the claim. -/
def validateAtomic (typingFuel normalizationFuel : Nat) (env : Environment) (term : Term) (claim : AtomicClaim) : Bool :=
  Checker.check typingFuel env [] true term claim.type &&
    (Conversion.normalize? env normalizationFuel term).any evidenceHead

theorem validateAtomic_sound {claim : AtomicClaim} (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (accepted : validateAtomic typingFuel normalizationFuel env term claim = true) : claim.Holds := by
  obtain ⟨checked,observed⟩ := Bool.and_eq_true_iff.mp accepted
  have typed := Checker.check_sound checked
  obtain ⟨output,normalized,recognized⟩ := (Option.any_eq_true _ _).mp observed
  exact AtomicClaim.realized history.wellFormed (evidenceHead_realize
    (typed.ghostNormalize history normalized) recognized)

theorem false_claim_rejected {claim : AtomicClaim} (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (falseClaim : ¬ claim.Holds) : validateAtomic typingFuel normalizationFuel env term claim = false := by
  cases accepted : validateAtomic typingFuel normalizationFuel env term claim with
  | false => rfl
  | true => exact False.elim (falseClaim (validateAtomic_sound history accepted))

/-- Unconditional consistency on the observed native fragment, with any number
of intervening conversions and every full-judgment rule inside subcomputations. -/
theorem no_closed_observed_false_equality (wf : UnifiedProgram.EnvWellFormed env) (different : m ≠ n)
    (typed : HasType env [] mode term (.eq (.natural m) (.natural n)))
    (recognized : evidenceHead term = true) : False :=
  AtomicTruth.no_false_equality wf different (evidenceHead_realize typed recognized)

theorem no_closed_observed_false_less (wf : UnifiedProgram.EnvWellFormed env) (unordered : ¬ m < n)
    (typed : HasType env [] mode term (.lt (.natural m) (.natural n)))
    (recognized : evidenceHead term = true) : False :=
  AtomicTruth.no_false_less wf unordered (evidenceHead_realize typed recognized)

end Jihoo.NativeKernel.Environment.Semantics
