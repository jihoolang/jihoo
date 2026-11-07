import Jihoo.GraphCertificateTyping

/-! Kernel-checked witnesses and boundaries for the target metatheory.
No contextual beta conversion, regularity assumption, or typing rule is added. -/
namespace Jihoo.CoreBridge.Raw.Examples

def empty : Context := fun _ => none
def malformed : Context := fun | 0 => some (.natural 0) | _ => none

theorem malformed_lookup : HasType malformed (.var 0) (.natural 0) := .var rfl

theorem malformed_not_formed : ¬ IsType malformed (.natural 0) := by
  intro h
  cases h

theorem arbitrary_substitution_changes_proposition :
    ((Raw.var 0).subst (single (.eq (.natural 0) (.natural 0)))).proposition ≠
      (Raw.var 0).proposition := by simp [subst, single, proposition]

/-- The replacement is genuinely open, and its index rises under both binders.
The inner erased binder has a dependent annotation mentioning the replaced term. -/
def nestedBody : Raw :=
  .lam false .u64 (.lam true (.eq (.var 1) (.var 1)) (.refl (.var 2)))
def nestedType : Raw :=
  .pi false .u64 (.pi true (.eq (.var 1) (.var 1)) (.eq (.var 2) (.var 2)))
def one : Context := empty.extend .u64

theorem nested_body_typed : HasType (one.extend .u64) nestedBody nestedType := by
  apply HasType.lam IsType.u64 rfl
  apply HasType.lam
  · exact .eq (.var (by simp [Context.extend, rename])) (.var (by simp [Context.extend, rename]))
  · rfl
  · exact .refl (.var (by simp [Context.extend, rename]))

theorem nested_open_substitution :
    HasType one
      (.lam false .u64 (.lam true (.eq (.var 1) (.var 1)) (.refl (.var 2))))
      (.pi false .u64 (.pi true (.eq (.var 1) (.var 1)) (.eq (.var 2) (.var 2)))) := by
  simpa [nestedBody, nestedType, subst, single, liftSub, rename] using
    nested_body_typed.instantiate (a := .var 0) (.var (by simp [one, Context.extend, rename]))

theorem nested_capture_avoidance :
    nestedBody.subst (single (.var 0)) = nestedBody := by
  simp [nestedBody, subst, single, liftSub, rename]

private theorem numeral {Γ : Context} (n : Nat) (h : n < wordBound) :
    HasType Γ (.natural n) .u64 := .natural h

def arithmeticBody : Raw := .refl (.uadd (.var 0) (.natural 1))
def arithmeticApplication : Raw := .app (.lam false .u64 arithmeticBody) (.natural 2)

theorem arithmetic_outer_conversion :
    Conv (.eq (.uadd (.natural 2) (.natural 1)) (.uadd (.natural 2) (.natural 1)))
      (.eq (.natural 3) (.natural 3)) :=
  .eq (.add 2 1 (by decide)) (.add 2 1 (by decide))

theorem arithmetic_conversion_not_reflexive :
    Raw.eq (.uadd (.natural 2) (.natural 1)) (.uadd (.natural 2) (.natural 1)) ≠
      .eq (.natural 3) (.natural 3) := by intro h; cases h

theorem arithmetic_application_typed :
    HasType empty arithmeticApplication (.eq (.natural 3) (.natural 3)) := by
  apply HasType.convert (A := .eq (.uadd (.natural 2) (.natural 1))
    (.uadd (.natural 2) (.natural 1)))
  · have hb : HasType (empty.extend .u64) arithmeticBody
        (.eq (.uadd (.var 0) (.natural 1)) (.uadd (.var 0) (.natural 1))) :=
      .refl (.uadd (.var (by simp [Context.extend, rename])) (.natural (by decide)))
    simpa [arithmeticApplication, subst, single, proposition] using
      HasType.app (.lam .u64 rfl hb) (numeral (Γ := empty) 2 (by decide))
  · exact arithmetic_outer_conversion

theorem arithmetic_head_beta :
    HasType empty (.refl (.uadd (.natural 2) (.natural 1)))
      (.eq (.natural 3) (.natural 3)) := by
  simpa [arithmeticBody, subst, single] using arithmetic_application_typed.head_beta

open Jihoo.GraphCertificates

def substitutionCertificate : Certificate := {
  before := #[.var 0, .refl 0, .natural 7]
  after := #[.var 0, .refl 0, .natural 7, .refl 2]
  input := 1
  output := 3
  operation := .substitute 2
}

theorem substitution_certificate_accepted : validate substitutionCertificate = true := by
  have hi : decode substitutionCertificate.before substitutionCertificate.input = some (.refl (.var 0)) := rfl
  have ho : decode substitutionCertificate.after substitutionCertificate.output = some (.refl (.natural 7)) := rfl
  have hv : decode substitutionCertificate.before 2 = some (.natural 7) := rfl
  have hp : appendOnly substitutionCertificate = true := by decide
  have hs : substitutionSafe substitutionCertificate 2 = true := by decide
  have hop : substitutionCertificate.operation = .substitute 2 := rfl
  simp only [validate, hp, hi, ho, ↓reduceIte, expected, hop, hs, hv]
  simp [subst, single, rawEqual]

theorem accepted_substitution_output_typed :
    ∃ output, decode substitutionCertificate.after substitutionCertificate.output = some output ∧
      Represents substitutionCertificate.after substitutionCertificate.output output ∧
      HasType empty output (.eq (.natural 7) (.natural 7)) := by
  simpa [subst, single] using validate_substitute_typed substitution_certificate_accepted rfl
    (show decode substitutionCertificate.before 1 = some (.refl (.var 0)) by rfl)
    (show decode substitutionCertificate.before 2 = some (.natural 7) by rfl)
    (show HasType (empty.extend .u64) (.refl (.var 0)) (.eq (.var 0) (.var 0))
      from .refl (.var (by simp [Context.extend, rename])))
    (show HasType empty (.natural 7) .u64 from .natural (by decide))

theorem accepted_substitution_exact_output :
    HasType empty (.refl (.natural 7)) (.eq (.natural 7) (.natural 7)) := by
  obtain ⟨output, hd, _, ht⟩ := accepted_substitution_output_typed
  have hd' : decode substitutionCertificate.after substitutionCertificate.output =
      some (.refl (.natural 7)) := rfl
  rw [hd'] at hd
  cases hd
  exact ht

/-- A beta redex used as an argument to a genuinely dependent function. -/
def argumentRedex : Raw := .app (.lam false .u64 (.var 0)) (.natural 0)
def dependentFunction : Raw := .lam false .u64 (.refl (.var 0))

private theorem identity_typed : HasType empty (.lam false .u64 (.var 0)) (.pi false .u64 .u64) :=
  .lam .u64 rfl (.var (by simp [Context.extend, rename]))

private theorem dependent_function_typed : HasType empty dependentFunction
    (.pi false .u64 (.eq (.var 0) (.var 0))) :=
  .lam .u64 rfl (.refl (.var (by simp [Context.extend, rename])))

theorem argument_redex_typed : HasType empty argumentRedex .u64 := by
  simpa [argumentRedex, subst] using HasType.app identity_typed (numeral (Γ := empty) 0 (by decide))

theorem dependent_before_typed :
    HasType empty (.app dependentFunction argumentRedex) (.eq argumentRedex argumentRedex) := by
  simpa [subst, single] using HasType.app dependent_function_typed argument_redex_typed

theorem dependent_after_typed :
    HasType empty (.app dependentFunction (.natural 0)) (.eq (.natural 0) (.natural 0)) := by
  simpa [subst, single] using HasType.app dependent_function_typed (numeral (Γ := empty) 0 (by decide))

/-- Conversion can inspect Eq/Lt/Array children but has no beta rule. -/
def appObserver : Raw → Bool
  | .app _ _ => true
  | .eq a b | .lt a b => appObserver a || appObserver b
  | .array a => appObserver a
  | _ => false

theorem conversion_preserves_app_observer (h : Conv A B) : appObserver A = appObserver B := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | add => rfl
  | eq _ _ ih₁ ih₂ => simp only [appObserver, ih₁, ih₂]
  | lt _ _ ih₁ ih₂ => simp only [appObserver, ih₁, ih₂]
  | array _ ih => exact ih

theorem dependent_result_types_not_convertible :
    ¬ Conv (.eq (.natural 0) (.natural 0)) (.eq argumentRedex argumentRedex) := by
  intro h
  have bad := conversion_preserves_app_observer h
  contradiction

/-- Inversion only for refl, including any outer conversions. -/
private theorem refl_result_conversion (h : HasType Γ t T) :
    ∀ a, t = .refl a → Conv (.eq a a) T := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True) <;>
    first | trivial | (intros a heq; cases heq)
  case refl => exact .refl _
  case convert hc ht ih => exact .trans (ih _ rfl) hc

/-- The contextual beta step fails to preserve this exact dependent result type,
not merely the particular typing derivations exhibited above. -/
theorem dependent_after_not_original_type :
    ¬ HasType empty (.app dependentFunction (.natural 0)) (.eq argumentRedex argumentRedex) := by
  intro h
  have hb : HasType empty (.refl (.natural 0)) (.eq argumentRedex argumentRedex) := by
    simpa [subst, single] using h.head_beta
  exact dependent_result_types_not_convertible (refl_result_conversion hb _ rfl)

def shiftCertificate : Certificate :=
  ⟨#[.var 0], #[.var 0, .var 1], 0, 1, .shift 1⟩

theorem shift_certificate_accepted : validate shiftCertificate = true := by
  have hi : decode shiftCertificate.before shiftCertificate.input = some (.var 0) := rfl
  have ho : decode shiftCertificate.after shiftCertificate.output = some (.var 1) := rfl
  have hp : appendOnly shiftCertificate = true := by decide
  simp only [validate, hp, hi, ho, ↓reduceIte]
  simp [expected, shiftCertificate, rename, rawEqual, signedBound]

theorem accepted_shift_output_typed :
    ∃ output, decode shiftCertificate.after shiftCertificate.output = some output ∧
      Represents shiftCertificate.after shiftCertificate.output output ∧
      HasType (one.extend .u64) output .u64 := by
  have hr : Renaming one (one.extend .u64) (fun k => k + 1) := Renaming.weaken one .u64
  simpa [rename] using validate_shift_typed shift_certificate_accepted rfl
    (show decode shiftCertificate.before shiftCertificate.input = some (.var 0) from rfl)
    (show HasType one (.var 0) .u64 from .var (by simp [one, Context.extend, rename])) hr

end Jihoo.CoreBridge.Raw.Examples
