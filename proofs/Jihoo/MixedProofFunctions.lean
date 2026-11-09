import Jihoo.Semantics

/-! Natural-index universal quantification and proof-domain functions, with
separate finite namespaces. Proofs never occur in index expressions. -/
namespace Jihoo.MixedProofFunctions
open Arithmetic (Expr Env)
open Indexed (Substitution shift lift single extendEnv ScopedSubstitution)

inductive Formula where
  | eq : Expr → Expr → Formula
  | lt : Expr → Expr → Formula
  | all : Formula → Formula
  | arrow : Formula → Formula → Formula
  deriving DecidableEq, Repr

def Formula.subst (σ : Substitution) : Formula → Formula
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .lt a b => .lt (a.subst σ) (b.subst σ)
  | .all B => .all (B.subst (lift σ))
  | .arrow A B => .arrow (A.subst σ) (B.subst σ)

def Formula.Scoped (n : Nat) : Formula → Prop
  | .eq a b | .lt a b => a.Scoped n ∧ b.Scoped n
  | .all B => B.Scoped (n + 1)
  | .arrow A B => A.Scoped n ∧ B.Scoped n

theorem Formula.scoped_subst {A : Formula} (h : A.Scoped n) (hs : ScopedSubstitution n m σ) :
    (A.subst σ).Scoped m := by
  induction A generalizing n m σ with
  | eq => exact ⟨Expr.scoped_subst h.1 hs, Expr.scoped_subst h.2 hs⟩
  | lt => exact ⟨Expr.scoped_subst h.1 hs, Expr.scoped_subst h.2 hs⟩
  | all B ih => exact ih h (Indexed.scoped_lift hs)
  | arrow A B ha hb => exact ⟨ha h.1 hs, hb h.2 hs⟩

@[simp] theorem Formula.subst_id (A : Formula) : A.subst Expr.var = A := by
  induction A <;> simp_all [Formula.subst]

theorem Formula.subst_comp (A : Formula) (σ τ : Substitution) :
    (A.subst σ).subst τ = A.subst (fun n => (σ n).subst τ) := by
  induction A generalizing σ τ <;>
    simp_all [Formula.subst, Indexed.expr_subst_comp, Indexed.lift_comp]

theorem Formula.shift_lift (A : Formula) (σ : Substitution) :
    (A.subst shift).subst (lift σ) = (A.subst σ).subst shift := by
  simp only [Formula.subst_comp]
  rfl

theorem Formula.instantiate_subst (A : Formula) (a : Expr) (σ : Substitution) :
    (A.subst (single a)).subst σ =
    (A.subst (lift σ)).subst (single (a.subst σ)) := by
  simp only [Formula.subst_comp, Indexed.lift_single]

inductive Term where
  | hyp : Nat → Term
  | refl : Expr → Term
  | decide : Nat → Nat → Term
  | zeroLe : Expr → Term
  | naturalLam : Term → Term
  | naturalApp : Term → Expr → Term
  | proofLam : Formula → Term → Term
  | proofApp : Term → Term → Term
  deriving DecidableEq, Repr

def Term.subst (σ : Substitution) : Term → Term
  | .hyp x => .hyp x
  | .refl a => .refl (a.subst σ)
  | .decide m n => .decide m n
  | .zeroLe a => .zeroLe (a.subst σ)
  | .naturalLam t => .naturalLam (t.subst (lift σ))
  | .naturalApp f a => .naturalApp (f.subst σ) (a.subst σ)
  | .proofLam A t => .proofLam (A.subst σ) (t.subst σ)
  | .proofApp f a => .proofApp (f.subst σ) (a.subst σ)

def Term.rename (ρ : Nat → Nat) : Term → Term
  | .hyp x => .hyp (ρ x)
  | .refl a => .refl a
  | .decide m n => .decide m n
  | .zeroLe a => .zeroLe a
  | .naturalLam t => .naturalLam (t.rename ρ)
  | .naturalApp f a => .naturalApp (f.rename ρ) a
  | .proofLam A t => .proofLam A (t.rename (Indexed.liftRenaming ρ))
  | .proofApp f a => .proofApp (f.rename ρ) (a.rename ρ)

def liftProofs (υ : Nat → Term) : Nat → Term
  | 0 => .hyp 0
  | x + 1 => (υ x).rename Nat.succ

def Term.proofSubst (υ : Nat → Term) : Term → Term
  | .hyp x => υ x
  | .refl a => .refl a
  | .decide m n => .decide m n
  | .zeroLe a => .zeroLe a
  | .naturalLam t => .naturalLam (t.proofSubst (fun x => (υ x).subst shift))
  | .naturalApp f a => .naturalApp (f.proofSubst υ) a
  | .proofLam A t => .proofLam A (t.proofSubst (liftProofs υ))
  | .proofApp f a => .proofApp (f.proofSubst υ) (a.proofSubst υ)

/-- Exact proposition matching, without general conversion or proof-dependent
indices. Every hypothesis and new proof annotation must be in natural scope. -/
inductive Derives : Nat → List Formula → Term → Formula → Prop where
  | hyp : Γ[x]? = some A → A.Scoped n → Derives n Γ (.hyp x) A
  | refl : a.Scoped n → Derives n Γ (.refl a) (.eq a a)
  | decide : m < k → Derives n Γ (.decide m k) (.lt (.lit m) (.lit k))
  | zeroLe : a.Scoped n → Derives n Γ (.zeroLe a) (.lt (.lit 0) (.add a (.lit 1)))
  | naturalLam : Derives (n + 1) (Γ.map (fun P => P.subst shift)) t B →
      Derives n Γ (.naturalLam t) (.all B)
  | naturalApp : Derives n Γ f (.all B) → a.Scoped n →
      Derives n Γ (.naturalApp f a) (B.subst (single a))
  | proofLam : A.Scoped n → Derives n (A :: Γ) t B →
      Derives n Γ (.proofLam A t) (.arrow A B)
  | proofApp : Derives n Γ f (.arrow A B) → Derives n Γ a A →
      Derives n Γ (.proofApp f a) B

theorem Derives.scoped (h : Derives n Γ t A) : A.Scoped n := by
  induction h with
  | hyp _ hs => exact hs
  | refl hs => exact ⟨hs, hs⟩
  | decide => exact ⟨trivial, trivial⟩
  | zeroLe hs => exact ⟨trivial, hs, trivial⟩
  | naturalLam _ ih => exact ih
  | naturalApp _ hs ih => exact Formula.scoped_subst ih (Indexed.scoped_single hs)
  | proofLam hs _ ih => exact ⟨hs, ih⟩
  | proofApp _ _ ih _ => exact ih.2

theorem Derives.scalar_substitution (h : Derives n Γ t A)
    (hs : ScopedSubstitution n m σ) :
    Derives m (Γ.map (fun P => P.subst σ)) (t.subst σ) (A.subst σ) := by
  induction h generalizing m σ with
  | hyp hx ha => exact .hyp (by simp [List.getElem?_map, hx]) (Formula.scoped_subst ha hs)
  | refl ha => exact .refl (Expr.scoped_subst ha hs)
  | decide h => exact .decide h
  | zeroLe ha => exact .zeroLe (Expr.scoped_subst ha hs)
  | naturalLam _ ih =>
      apply Derives.naturalLam
      simpa only [List.map_map, Function.comp_def, Formula.shift_lift] using ih (Indexed.scoped_lift hs)
  | naturalApp _ ha ih =>
      simp only [Term.subst, Formula.instantiate_subst]
      exact .naturalApp (ih hs) (Expr.scoped_subst ha hs)
  | proofLam ha _ ih => exact .proofLam (Formula.scoped_subst ha hs) (ih hs)
  | proofApp _ _ hf ha => exact .proofApp (hf hs) (ha hs)

theorem Derives.renaming (h : Derives n Γ t A) (ρ : Nat → Nat)
    (hr : ∀ x P, Γ[x]? = some P → Δ[ρ x]? = some P) :
    Derives n Δ (t.rename ρ) A := by
  induction h generalizing Δ ρ with
  | hyp hx hs => exact .hyp (hr _ _ hx) hs
  | refl hs => exact .refl hs
  | decide h => exact .decide h
  | zeroLe hs => exact .zeroLe hs
  | @naturalLam n t B Γ _ ih =>
      apply Derives.naturalLam
      apply ih ρ
      intro x P hx
      simp only [List.getElem?_map] at hx ⊢
      cases he : Γ[x]? with
      | none => simp [he] at hx
      | some Q =>
          simp only [he, Option.map_some, Option.some.injEq] at hx
          simp [hr x Q he, hx]
  | naturalApp _ hs ih => exact .naturalApp (ih ρ hr) hs
  | proofLam hs _ ih =>
      apply Derives.proofLam hs
      apply ih (Indexed.liftRenaming ρ)
      intro x P hx
      cases x with
      | zero => exact hx
      | succ x => exact hr x P hx
  | proofApp _ _ hf ha => exact .proofApp (hf ρ hr) (ha ρ hr)

theorem Derives.proof_substitution (h : Derives n Γ t A) (υ : Nat → Term)
    (hu : ∀ x P, Γ[x]? = some P → Derives n Δ (υ x) P) :
    Derives n Δ (t.proofSubst υ) A := by
  induction h generalizing Δ υ with
  | hyp hx _ => exact hu _ _ hx
  | refl hs => exact .refl hs
  | decide h => exact .decide h
  | zeroLe hs => exact .zeroLe hs
  | @naturalLam n t B Γ _ ih =>
      apply Derives.naturalLam
      apply ih (fun x => (υ x).subst shift)
      intro x P hx
      simp only [List.getElem?_map] at hx
      cases he : Γ[x]? with
      | none => simp [he] at hx
      | some Q =>
          simp only [he, Option.map_some, Option.some.injEq] at hx
          subst P
          exact (hu x Q he).scalar_substitution Indexed.scoped_shift
  | naturalApp _ hs ih => exact .naturalApp (ih υ hu) hs
  | proofLam hs _ ih =>
      apply Derives.proofLam hs
      apply ih (liftProofs υ)
      intro x P hx
      cases x with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst P
          exact .hyp rfl hs
      | succ x => exact (hu x P hx).renaming Nat.succ (fun _ _ h => h)
  | proofApp _ _ hf ha => exact .proofApp (hf υ hu) (ha υ hu)

@[simp] theorem Formula.shift_single (A : Formula) (a : Expr) :
    (A.subst shift).subst (single a) = A := by
  rw [Formula.subst_comp]
  exact A.subst_id

def singleProof (v : Term) : Nat → Term
  | 0 => v
  | x + 1 => .hyp x

theorem natural_beta (h : Derives (n + 1) (Γ.map (fun P => P.subst shift)) body B)
    (ha : a.Scoped n) : Derives n Γ (body.subst (single a)) (B.subst (single a)) := by
  simpa [List.map_map, Function.comp_def, Formula.shift_single]
    using h.scalar_substitution (Indexed.scoped_single ha)

theorem proof_beta (h : Derives n (A :: Γ) body B) (hv : Derives n Γ v A)
    (hΓ : ∀ P ∈ Γ, P.Scoped n) :
    Derives n Γ (body.proofSubst (singleProof v)) B := by
  apply h.proof_substitution (singleProof v)
  intro x P hx
  cases x with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst P; exact hv
  | succ x =>
      exact .hyp hx (hΓ P (List.mem_of_getElem? hx))

def Formula.Holds (ρ : Env) : Formula → Prop
  | .eq a b => a.eval ρ = b.eval ρ
  | .lt a b => a.eval ρ < b.eval ρ
  | .all B => ∀ a, B.Holds (extendEnv ρ a)
  | .arrow A B => A.Holds ρ → B.Holds ρ

theorem Formula.holds_subst (A : Formula) (σ : Substitution) (ρ : Env) :
    (A.subst σ).Holds ρ ↔ A.Holds (fun x => (σ x).eval ρ) := by
  induction A generalizing σ ρ with
  | eq => simp [Formula.subst, Formula.Holds, Expr.eval_subst]
  | lt => simp [Formula.subst, Formula.Holds, Expr.eval_subst]
  | all B ih =>
      simp only [Formula.subst, Formula.Holds]
      apply forall_congr'
      intro a
      simpa only [Indexed.lift_eval] using ih (lift σ) (extendEnv ρ a)
  | arrow A B ha hb => exact imp_congr (ha σ ρ) (hb σ ρ)

def Valid (Γ : List Formula) (ρ : Env) : Prop := ∀ (x : Nat) (P : Formula), Γ[x]? = some P → P.Holds ρ

theorem Derives.sound (h : Derives n Γ t A) (hv : Valid Γ ρ) : A.Holds ρ := by
  induction h generalizing ρ with
  | hyp hx _ => exact hv _ _ hx
  | refl => rfl
  | decide h => exact h
  | zeroLe => exact Nat.zero_lt_succ _
  | @naturalLam n t B Γ _ ih =>
      intro a
      apply ih
      intro x P hx
      simp only [List.getElem?_map] at hx
      cases he : Γ[x]? with
      | none => simp [he] at hx
      | some Q =>
          simp only [he, Option.map_some, Option.some.injEq] at hx
          subst P
          exact (Q.holds_subst shift (extendEnv ρ a)).mpr (hv x Q he)
  | @naturalApp n Γ f B a _ _ ih =>
      apply (B.holds_subst (single a) ρ).mpr
      have he : (fun x => (single a x).eval ρ) = extendEnv ρ (a.eval ρ) := by
        funext x
        cases x <;> rfl
      rw [he]
      exact ih hv (a.eval ρ)
  | proofLam _ _ ih =>
      intro ha
      apply ih
      intro x P hx
      cases x with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst P; exact ha
      | succ x => exact hv x P hx
  | proofApp _ _ hf ha => exact hf hv (ha hv)

theorem no_false_bound : ¬ Derives 0 [] t (.lt (.lit k) (.lit k)) := by
  intro h
  exact Nat.lt_irrefl k (h.sound (ρ := fun _ => 0) (by intro x P hx; simp at hx))

theorem no_false_equality (hne : m ≠ n) : ¬ Derives 0 [] t (.eq (.lit m) (.lit n)) := by
  intro h
  exact hne (h.sound (ρ := fun _ => 0) (by intro x P hx; simp at hx))

end Jihoo.MixedProofFunctions
