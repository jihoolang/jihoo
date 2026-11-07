import Jihoo.Arithmetic

/-! An extrinsically typed, index-dependent function calculus. Only natural
indices are bound by lambdas; values are bound by nondependent lets. This is not
the full core calculus. See the proof boundary document for the correspondence. -/
namespace Jihoo.Indexed

open Arithmetic (Expr)

abbrev Substitution := Nat → Expr

def shift : Substitution := fun n => .var (n + 1)
def single (a : Expr) : Substitution
  | 0 => a
  | n + 1 => .var n

def lift (σ : Substitution) : Substitution
  | 0 => .var 0
  | n + 1 => (σ n).subst shift

@[simp] theorem expr_subst_id (t : Expr) : t.subst Expr.var = t := by
  induction t <;> simp_all [Expr.subst]

theorem expr_subst_comp (t : Expr) (σ τ : Substitution) :
    (t.subst σ).subst τ = t.subst (fun n => (σ n).subst τ) := by
  induction t <;> simp_all [Expr.subst]

@[simp] theorem lift_id : lift Expr.var = Expr.var := by
  funext n
  cases n <;> rfl

theorem shift_lift (σ : Substitution) (t : Expr) :
    (t.subst shift).subst (lift σ) = (t.subst σ).subst shift := by
  simp only [expr_subst_comp]
  rfl

theorem lift_comp (σ τ : Substitution) :
    (fun n => (lift σ n).subst (lift τ)) = lift (fun n => (σ n).subst τ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact shift_lift τ (σ n)

@[simp] theorem shift_single (t a : Expr) :
    (t.subst shift).subst (single a) = t := by
  rw [expr_subst_comp]
  exact expr_subst_id t

theorem lift_single (σ : Substitution) (a : Expr) :
    (fun n => (lift σ n).subst (single (a.subst σ))) =
      (fun n => (single a n).subst σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact shift_single (σ n) (a.subst σ)

inductive Ty where
  | u64
  | i64
  | array : Expr → Ty
  | lt : Expr → Expr → Ty
  | eq : Expr → Expr → Ty
  | pi : Ty → Ty
  deriving DecidableEq, Repr

def Ty.subst (σ : Substitution) : Ty → Ty
  | .u64 => .u64
  | .i64 => .i64
  | .array n => .array (n.subst σ)
  | .lt a b => .lt (a.subst σ) (b.subst σ)
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .pi body => .pi (body.subst (lift σ))

@[simp] theorem Ty.subst_id (A : Ty) : A.subst Expr.var = A := by
  induction A <;> simp_all [Ty.subst]

theorem Ty.subst_comp (A : Ty) (σ τ : Substitution) :
    (A.subst σ).subst τ = A.subst (fun n => (σ n).subst τ) := by
  induction A generalizing σ τ <;> simp_all [Ty.subst, expr_subst_comp, lift_comp]

theorem Ty.shift_lift (A : Ty) (σ : Substitution) :
    (A.subst shift).subst (lift σ) = (A.subst σ).subst shift := by
  simp only [Ty.subst_comp]
  rfl

@[simp] theorem Ty.shift_single (A : Ty) (a : Expr) :
    (A.subst shift).subst (single a) = A := by
  rw [Ty.subst_comp]
  exact A.subst_id

theorem Ty.instantiate_subst (A : Ty) (a : Expr) (σ : Substitution) :
    (A.subst (single a)).subst σ =
      (A.subst (lift σ)).subst (single (a.subst σ)) := by
  simp only [Ty.subst_comp, lift_single]

/-- Value variables are separate from the bound natural-index variables.
A context can mention the free indices, so binding an index weakens its types. -/
abbrev Context := Nat → Ty

def Context.extend (Γ : Context) (A : Ty) : Context
  | 0 => A
  | n + 1 => Γ n

def Context.subst (Γ : Context) (σ : Substitution) : Context :=
  fun x => (Γ x).subst σ

@[simp] theorem Context.extend_subst (Γ : Context) (A : Ty) (σ : Substitution) :
    (Γ.extend A).subst σ = (Γ.subst σ).extend (A.subst σ) := by
  funext x
  cases x <;> rfl

theorem Context.shift_lift (Γ : Context) (σ : Substitution) :
    (Γ.subst shift).subst (lift σ) = (Γ.subst σ).subst shift := by
  funext x
  exact (Γ x).shift_lift σ

@[simp] theorem Context.shift_single (Γ : Context) (a : Expr) :
    (Γ.subst shift).subst (single a) = Γ := by
  funext x
  exact (Γ x).shift_single a

inductive Term where
  | param : Nat → Term
  | natural : Expr → Term
  | integer : Int → Term
  | elements : List Int → Term
  | decide : Nat → Nat → Term
  | refl : Expr → Term
  | zeroLe : Expr → Term
  | index : Term → Expr → Term → Term
  | lam : Term → Term
  | app : Term → Expr → Term
  | letValue : Term → Term → Term
  deriving DecidableEq, Repr

def Term.subst (σ : Substitution) : Term → Term
  | .param x => .param x
  | .natural n => .natural (n.subst σ)
  | .integer n => .integer n
  | .elements ns => .elements ns
  | .decide m n => .decide m n
  | .refl a => .refl (a.subst σ)
  | .zeroLe a => .zeroLe (a.subst σ)
  | .index a i p => .index (a.subst σ) (i.subst σ) (p.subst σ)
  | .lam body => .lam (body.subst (lift σ))
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .letValue v body => .letValue (v.subst σ) (body.subst σ)

@[simp] theorem Term.subst_id (t : Term) : t.subst Expr.var = t := by
  induction t <;> simp_all [Term.subst]

theorem Term.subst_comp (t : Term) (σ τ : Substitution) :
    (t.subst σ).subst τ = t.subst (fun n => (σ n).subst τ) := by
  induction t generalizing σ τ <;>
    simp_all [Term.subst, expr_subst_comp, lift_comp]

theorem Term.instantiate_subst (t : Term) (a : Expr) (σ : Substitution) :
    (t.subst (single a)).subst σ =
      (t.subst (lift σ)).subst (single (a.subst σ)) := by
  simp only [Term.subst_comp, lift_single]

def liftRenaming (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def Term.renameValues (ρ : Nat → Nat) : Term → Term
  | .param x => .param (ρ x)
  | .natural n => .natural n
  | .integer n => .integer n
  | .elements ns => .elements ns
  | .decide m n => .decide m n
  | .refl a => .refl a
  | .zeroLe a => .zeroLe a
  | .index a i p => .index (a.renameValues ρ) i (p.renameValues ρ)
  | .lam body => .lam (body.renameValues ρ)
  | .app f a => .app (f.renameValues ρ) a
  | .letValue v body => .letValue (v.renameValues ρ) (body.renameValues (liftRenaming ρ))

def liftValues (σ : Nat → Term) : Nat → Term
  | 0 => .param 0
  | n + 1 => (σ n).renameValues Nat.succ

def singleValue (v : Term) : Nat → Term
  | 0 => v
  | n + 1 => .param n

def Term.valueSubst (σ : Nat → Term) : Term → Term
  | .param x => σ x
  | .natural n => .natural n
  | .integer n => .integer n
  | .elements ns => .elements ns
  | .decide m n => .decide m n
  | .refl a => .refl a
  | .zeroLe a => .zeroLe a
  | .index a i p => .index (a.valueSubst σ) i (p.valueSubst σ)
  | .lam body => .lam (body.valueSubst (fun x => (σ x).subst shift))
  | .app f a => .app (f.valueSubst σ) a
  | .letValue v body => .letValue (v.valueSubst σ) (body.valueSubst (liftValues σ))

theorem Term.renameValues_indexSubst (t : Term) (ρ : Nat → Nat) (σ : Substitution) :
    (t.renameValues ρ).subst σ = (t.subst σ).renameValues ρ := by
  induction t generalizing ρ σ <;> simp_all [Term.renameValues, Term.subst]

theorem Term.shift_lift (t : Term) (σ : Substitution) :
    (t.subst shift).subst (lift σ) = (t.subst σ).subst shift := by
  simp only [Term.subst_comp]
  rfl

theorem liftValues_indexSubst (υ : Nat → Term) (σ : Substitution) :
    (fun x => (liftValues υ x).subst σ) = liftValues (fun x => (υ x).subst σ) := by
  funext x
  cases x with
  | zero => rfl
  | succ x => exact (υ x).renameValues_indexSubst Nat.succ σ

theorem Term.valueSubst_indexSubst (t : Term) (υ : Nat → Term) (σ : Substitution) :
    (t.valueSubst υ).subst σ = (t.subst σ).valueSubst (fun x => (υ x).subst σ) := by
  induction t generalizing υ σ <;>
    simp_all [Term.valueSubst, Term.subst, Term.shift_lift, liftValues_indexSubst]

/-- Extrinsic typing: raw syntax and reduction do not carry typing evidence.
Pi binds a natural index in the result type; lambda binds it in the body. -/
inductive HasType : Context → Term → Ty → Prop where
  | param (Γ x) : HasType Γ (.param x) (Γ x)
  | natural (Γ a) : HasType Γ (.natural a) .u64
  | integer (Γ n) : HasType Γ (.integer n) .i64
  | elements (Γ ns) : HasType Γ (.elements ns) (.array (.lit ns.length))
  | decide (Γ m n) : m < n → HasType Γ (.decide m n) (.lt (.lit m) (.lit n))
  | refl (Γ a) : HasType Γ (.refl a) (.eq a a)
  | zeroLe (Γ a) : HasType Γ (.zeroLe a) (.lt (.lit 0) (.add a (.lit 1)))
  | index : HasType Γ a (.array n) → HasType Γ p (.lt i n) →
      HasType Γ (.index a i p) .i64
  | lam : HasType (Γ.subst shift) body B → HasType Γ (.lam body) (.pi B)
  | app : HasType Γ f (.pi B) → HasType Γ (.app f a) (B.subst (single a))
  | letValue : HasType Γ v A → HasType (Γ.extend A) body B →
      HasType Γ (.letValue v body) B

/-- Capture-avoiding substitution preserves dependent typing, including beneath
Pi/lambda binders. No semantic typing hypothesis is used. -/
theorem HasType.substitution (h : HasType Γ t A) (σ : Substitution) :
    HasType (Γ.subst σ) (t.subst σ) (A.subst σ) := by
  induction h generalizing σ with
  | param => exact .param _ _
  | natural => exact .natural _ _
  | integer => exact .integer _ _
  | elements => exact .elements _ _
  | decide _ _ _ h => exact .decide _ _ _ h
  | refl => exact .refl _ _
  | zeroLe => exact .zeroLe _ _
  | index _ _ iha ihp => exact .index (iha σ) (ihp σ)
  | lam _ ih =>
      apply HasType.lam
      simpa only [Context.shift_lift] using ih (lift σ)
  | app h ih =>
      simp only [Term.subst, Ty.instantiate_subst]
      exact .app (ih σ)
  | letValue _ _ ihv ihb =>
      apply HasType.letValue (ihv σ)
      simpa only [Context.extend_subst] using ihb σ

/-- Renaming value variables preserves typing in correspondingly related contexts. -/
theorem HasType.valueRenaming (h : HasType Γ t A) (ρ : Nat → Nat)
    (hρ : ∀ x, Δ (ρ x) = Γ x) : HasType Δ (t.renameValues ρ) A := by
  induction h generalizing Δ ρ with
  | param Γ x => simpa only [hρ, Term.renameValues] using HasType.param Δ (ρ x)
  | natural => exact .natural _ _
  | integer => exact .integer _ _
  | elements => exact .elements _ _
  | decide _ _ _ h => exact .decide _ _ _ h
  | refl => exact .refl _ _
  | zeroLe => exact .zeroLe _ _
  | index _ _ iha ihp => exact .index (iha ρ hρ) (ihp ρ hρ)
  | lam _ ih =>
      apply HasType.lam
      apply ih ρ
      intro x
      simp only [Context.subst, hρ]
  | app _ ih => exact .app (ih ρ hρ)
  | letValue _ _ ihv ihb =>
      apply HasType.letValue (ihv ρ hρ)
      apply ihb (liftRenaming ρ)
      intro x
      cases x <;> simp [Context.extend, liftRenaming, hρ]

/-- A real value-substitution lemma. Under an index lambda the inserted values
are index-weakened; under a value let they are value-weakened. -/
theorem HasType.valueSubstitution (h : HasType Γ t A)
    (σ : Nat → Term) (hσ : ∀ x, HasType Δ (σ x) (Γ x)) :
    HasType Δ (t.valueSubst σ) A := by
  induction h generalizing Δ σ with
  | param Γ x => exact hσ x
  | natural => exact .natural _ _
  | integer => exact .integer _ _
  | elements => exact .elements _ _
  | decide _ _ _ h => exact .decide _ _ _ h
  | refl => exact .refl _ _
  | zeroLe => exact .zeroLe _ _
  | index _ _ iha ihp => exact .index (iha σ hσ) (ihp σ hσ)
  | lam _ ih =>
      apply HasType.lam
      apply ih (fun x => (σ x).subst shift)
      intro x
      exact (hσ x).substitution shift
  | app _ ih => exact .app (ih σ hσ)
  | letValue _ _ ihv ihb =>
      apply HasType.letValue (ihv σ hσ)
      apply ihb (liftValues σ)
      intro x
      cases x with
      | zero => exact .param _ 0
      | succ x => exact (hσ x).valueRenaming Nat.succ (fun _ => rfl)

/-- Pure index-beta and value-let reduction with compatible closure. In particular this relation is
on untyped terms: typing preservation is proved separately below. -/
inductive Step : Term → Term → Prop where
  | beta (body a) : Step (.app (.lam body) a) (body.subst (single a))
  | lam : Step a b → Step (.lam a) (.lam b)
  | app : Step f g → Step (.app f a) (.app g a)
  | indexArray : Step a b → Step (.index a i p) (.index b i p)
  | indexProof : Step p q → Step (.index a i p) (.index a i q)
  | letBeta (v body) : Step (.letValue v body) (body.valueSubst (singleValue v))
  | letArg : Step v w → Step (.letValue v body) (.letValue w body)
  | letBody : Step a b → Step (.letValue v a) (.letValue v b)

/-- Substitution also preserves the untyped reduction relation. -/
theorem Step.substitution (h : Step t u) (σ : Substitution) :
    Step (t.subst σ) (u.subst σ) := by
  induction h generalizing σ with
  | beta body a =>
      simp only [Term.subst, Term.instantiate_subst]
      exact .beta _ _
  | lam _ ih => exact .lam (ih (lift σ))
  | app _ ih => exact .app (ih σ)
  | indexArray _ ih => exact .indexArray (ih σ)
  | indexProof _ ih => exact .indexProof (ih σ)
  | letBeta v body =>
      simp only [Term.subst, Term.valueSubst_indexSubst]
      have same : (fun x => (singleValue v x).subst σ) = singleValue (v.subst σ) := by
        funext x
        cases x <;> rfl
      rw [same]
      exact .letBeta _ _
  | letArg _ ih => exact .letArg (ih σ)
  | letBody _ ih => exact .letBody (ih σ)

theorem preservation (h : HasType Γ t A) (step : Step t u) : HasType Γ u A := by
  induction step generalizing Γ A with
  | beta body a =>
      cases h with
      | app hf =>
          cases hf with
          | lam hb =>
              simpa only [Context.shift_single] using hb.substitution (single a)
  | lam _ ih =>
      cases h with
      | lam hb => exact .lam (ih hb)
  | app _ ih =>
      cases h with
      | app hf => exact .app (ih hf)
  | indexArray _ ih =>
      cases h with
      | index ha hp => exact .index (ih ha) hp
  | indexProof _ ih =>
      cases h with
      | index ha hp => exact .index ha (ih hp)
  | letBeta v body =>
      cases h with
      | letValue hv hb =>
          apply hb.valueSubstitution (singleValue v)
          intro x
          cases x with
          | zero => exact hv
          | succ x => exact .param _ x
  | letArg _ ih =>
      cases h with
      | letValue hv hb => exact .letValue (ih hv) hb
  | letBody _ ih =>
      cases h with
      | letValue hv hb => exact .letValue hv (ih hb)

inductive Steps : Term → Term → Prop where
  | refl (t) : Steps t t
  | next : Step t u → Steps u v → Steps t v

theorem preservation_many (h : HasType Γ t A) (steps : Steps t u) : HasType Γ u A := by
  induction steps with
  | refl => exact h
  | next hs _ ih => exact ih (preservation h hs)

end Jihoo.Indexed
