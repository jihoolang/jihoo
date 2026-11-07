import Jihoo.Arithmetic

/-! An extrinsically typed, index-dependent function calculus. Only natural
indices are bound by lambdas; value variables are free parameters. This is not
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

/-- Free value parameters are separate from the bound natural-index variables.
A context can mention the free indices, so binding an index weakens its types. -/
abbrev Context := Nat → Ty

def Context.subst (Γ : Context) (σ : Substitution) : Context :=
  fun x => (Γ x).subst σ

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

/-- Pure beta reduction and compatible closure. In particular this relation is
on untyped terms: typing preservation is proved separately below. -/
inductive Step : Term → Term → Prop where
  | beta (body a) : Step (.app (.lam body) a) (body.subst (single a))
  | lam : Step a b → Step (.lam a) (.lam b)
  | app : Step f g → Step (.app f a) (.app g a)
  | indexArray : Step a b → Step (.index a i p) (.index b i p)
  | indexProof : Step p q → Step (.index a i p) (.index a i q)

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

inductive Steps : Term → Term → Prop where
  | refl (t) : Steps t t
  | next : Step t u → Steps u v → Steps t v

theorem preservation_many (h : HasType Γ t A) (steps : Steps t u) : HasType Γ u A := by
  induction steps with
  | refl => exact h
  | next hs _ ih => exact ih (preservation h hs)

end Jihoo.Indexed
