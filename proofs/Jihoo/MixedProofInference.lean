import Jihoo.MixedProofTranslation

/-! Executable inference for the mixed natural/proof judgment. Completeness is
only for this exact-matching judgment, not the executable jihoo checker. -/
namespace Jihoo.MixedProofFunctions.Checked
open Arithmetic (Expr)
open Bridge

instance exprScope (n : Nat) (a : Expr) : Decidable (a.Scoped n) :=
  match a with
  | .var x => inferInstanceAs (Decidable (x < n))
  | .lit _ => isTrue trivial
  | .add a b | .sub a b => @instDecidableAnd _ _ (exprScope n a) (exprScope n b)

instance formulaScope (n : Nat) (A : Formula) : Decidable (A.Scoped n) :=
  match A with
  | .eq a b | .lt a b => inferInstanceAs (Decidable (a.Scoped n ∧ b.Scoped n))
  | .all B => formulaScope (n + 1) B
  | .arrow A B => @instDecidableAnd _ _ (formulaScope n A) (formulaScope n B)

instance indexAdmission (a : Expr) : Decidable (IndexAdmitted a) :=
  match a with
  | .var _ => isTrue trivial
  | .lit n => inferInstanceAs (Decidable (n < CoreBridge.wordBound))
  | .add a b => @instDecidableAnd _ _ (indexAdmission a) (indexAdmission b)
  | .sub _ _ => isFalse id

instance formulaAdmission (A : Formula) : Decidable (FormulaAdmitted A) :=
  match A with
  | .eq a b | .lt a b => @instDecidableAnd _ _ (indexAdmission a) (indexAdmission b)
  | .all B => formulaAdmission B
  | .arrow A B => @instDecidableAnd _ _ (formulaAdmission A) (formulaAdmission B)

instance termAdmission (t : Term) : Decidable (TermAdmitted t) :=
  match t with
  | .hyp _ => isTrue trivial
  | .refl a | .zeroLe a => indexAdmission a
  | .decide m n => inferInstanceAs (Decidable (m < CoreBridge.wordBound ∧ n < CoreBridge.wordBound))
  | .naturalLam t => termAdmission t
  | .naturalApp f a => @instDecidableAnd _ _ (termAdmission f) (indexAdmission a)
  | .proofLam A t => @instDecidableAnd _ _ (formulaAdmission A) (termAdmission t)
  | .proofApp f a => @instDecidableAnd _ _ (termAdmission f) (termAdmission a)

abbrev Result (n : Nat) (Γ : List Formula) (t : Term) := { A : Formula // Derives n Γ t A }

def infer (n : Nat) (Γ : List Formula) (t : Term) : Option (Result n Γ t) :=
  match t with
  | .hyp x => match hx : Γ[x]? with
    | none => none
    | some A => if hs : A.Scoped n then some ⟨A, .hyp hx hs⟩ else none
  | .refl a => if hs : a.Scoped n then some ⟨.eq a a, .refl hs⟩ else none
  | .decide m k => if h : m < k then some ⟨.lt (.lit m) (.lit k), .decide h⟩ else none
  | .zeroLe a => if hs : a.Scoped n then some ⟨.lt (.lit 0) (.add a (.lit 1)), .zeroLe hs⟩ else none
  | .naturalLam t => do
      let ⟨B, hb⟩ ← infer (n + 1) (Γ.map (fun A => A.subst Indexed.shift)) t
      return ⟨.all B, .naturalLam hb⟩
  | .naturalApp f a => do
      let ⟨F, hf⟩ ← infer n Γ f
      match he : F with
      | .all B => if hs : a.Scoped n then
          some ⟨B.subst (Indexed.single a), .naturalApp (he ▸ hf) hs⟩ else none
      | _ => none
  | .proofLam A t => if hs : A.Scoped n then do
      let ⟨B, hb⟩ ← infer n (A :: Γ) t
      return ⟨.arrow A B, .proofLam hs hb⟩
      else none
  | .proofApp f a => do
      let ⟨F, hf⟩ ← infer n Γ f
      match he : F with
      | .arrow A B =>
          let ⟨P, hp⟩ ← infer n Γ a
          if ha : P = A then some ⟨B, .proofApp (he ▸ hf) (ha ▸ hp)⟩ else none
      | _ => none

theorem infer_complete (h : Derives n Γ t A) : infer n Γ t = some ⟨A, h⟩ := by
  induction h with
  | @hyp Γ x A n hx hs =>
      unfold infer
      split
      next he => simp [hx] at he
      next B he =>
        have same : B = A := Option.some.inj (he.symm.trans hx)
        subst B
        simp [hs]
  | refl hs => simp [infer, hs]
  | decide h => simp [infer, h]
  | zeroLe hs => simp [infer, hs]
  | naturalLam _ ih => simp [infer, ih]
  | naturalApp _ hs ih => simp [infer, ih, hs]
  | proofLam hs _ ih => simp [infer, hs, ih]
  | proofApp _ _ hf ha => simp [infer, hf, ha]

def inferType (n : Nat) (Γ : List Formula) (t : Term) : Option Formula :=
  (infer n Γ t).map Subtype.val

theorem inferType_iff : inferType n Γ t = some A ↔ Derives n Γ t A := by
  constructor
  · intro h
    unfold inferType at h
    cases hi : infer n Γ t with
    | none => simp [hi] at h
    | some result =>
        simp only [hi, Option.map_some, Option.some.injEq] at h
        exact h ▸ result.property
  · intro h
    simp [inferType, infer_complete h]

theorem accepted_sound (h : inferType n Γ t = some A) (hv : Valid Γ ρ) : A.Holds ρ :=
  (inferType_iff.mp h).sound hv

theorem rejected_iff : inferType n Γ t = none ↔ ∀ A, ¬ Derives n Γ t A := by
  constructor
  · intro h A ht
    have accepted := inferType_iff.mpr ht
    rw [h] at accepted
    contradiction
  · intro h
    cases hi : inferType n Γ t with
    | none => rfl
    | some A => exact False.elim (h A (inferType_iff.mp hi))

end Jihoo.MixedProofFunctions.Checked
