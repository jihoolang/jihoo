import Jihoo.CoreBridgeBetaShapes
import Jihoo.CoreBridgeBetaPreservation

/-! Conversion-stable simple typing of the existing higher-order Raw calculus.
This is a structural erasure theorem, not a semantic interpretation of indices,
a normalization theorem, or a translation of runtime/compiler erasure. -/
namespace Jihoo.CoreBridge.Raw.Beta.SimpleErasure

inductive Ty where
  | base
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- All scalar, array and proposition indices collapse to one base sort.
Higher-order function domains/codomains remain; binder modes are erased. -/
inductive Shape : Raw → Ty → Prop where
  | u64 : Shape .u64 .base
  | i64 : Shape .i64 .base
  | array : Shape (.array n) .base
  | lt : Shape (.lt a b) .base
  | eq : Shape (.eq a b) .base
  | pi : Shape A a → Shape B b → Shape (.pi e A B) (.arrow a b)

theorem Shape.substitution (h : Shape A a) (σ : Nat → Raw) : Shape (A.subst σ) a := by
  induction h generalizing σ <;> simp only [Raw.subst]
  case u64 => exact .u64
  case i64 => exact .i64
  case array => exact .array
  case lt => exact .lt
  case eq => exact .eq
  case pi hA hB ihA ihB => exact .pi (ihA σ) (ihB (liftSub σ))
theorem Shape.renaming (h : Shape A a) (ρ : Nat → Nat) : Shape (A.rename ρ) a := by
  induction h generalizing ρ <;> simp only [Raw.rename]
  case u64 => exact .u64
  case i64 => exact .i64
  case array => exact .array
  case lt => exact .lt
  case eq => exact .eq
  case pi hA hB ihA ihB => exact .pi (ihA ρ) (ihB (Jihoo.Indexed.liftRenaming ρ))

/-- Raw beta expansions may lack Shape. Uniqueness compares two structural
representatives and uses the already proved Church–Rosser injectivity results. -/
theorem Shape.conversion_unique (hA : Shape A a) (hB : Shape B b)
    (hc : Conv A B) : a = b := by
  induction hA generalizing B b with
  | u64 | i64 | array | lt | eq =>
      cases hB <;> first | rfl | (have hh := hc.rigid_head rfl rfl; contradiction)
  | pi hD hE ihD ihE =>
      cases hB <;> try (have hh := hc.rigid_head rfl rfl; contradiction)
      case pi hF hG =>
        obtain ⟨_, hd, he⟩ := hc.pi_injective
        rw [ihD hF hd, ihE hG he]

/-- A simple type belongs to the conversion class, rather than to the current
raw syntax. In particular, an unformed beta expansion can still have Arity. -/
def Arity (A : Raw) (a : Ty) : Prop := ∃ B, Conv A B ∧ Shape B a

theorem Shape.arity (h : Shape A a) : Arity A a := ⟨A, .refl _, h⟩

theorem Arity.unique (h : Arity A a) (h' : Arity A b) : a = b := by
  obtain ⟨B, hc, hs⟩ := h
  obtain ⟨C, hc', hs'⟩ := h'
  exact hs.conversion_unique hs' (hc.symm.trans hc')

theorem Arity.conversion (h : Arity A a) (hc : Conv A B) : Arity B a := by
  obtain ⟨C, hd, hs⟩ := h
  exact ⟨C, hc.symm.trans hd, hs⟩

theorem Arity.conversion_iff (hc : Conv A B) : Arity A a ↔ Arity B a :=
  ⟨fun h => h.conversion hc, fun h => h.conversion hc.symm⟩

theorem Arity.substitution (h : Arity A a) (σ : Nat → Raw) : Arity (A.subst σ) a := by
  obtain ⟨B, hc, hs⟩ := h
  exact ⟨B.subst σ, hc.substitution σ, hs.substitution σ⟩

theorem Arity.renaming (h : Arity A a) (ρ : Nat → Nat) : Arity (A.rename ρ) a := by
  obtain ⟨B, hc, hs⟩ := h
  exact ⟨B.rename ρ, hc.renaming ρ, hs.renaming ρ⟩

theorem Arity.pi (hA : Arity A a) (hB : Arity B b) : Arity (.pi e A B) (.arrow a b) := by
  obtain ⟨D, hd, hsD⟩ := hA
  obtain ⟨E, he, hsE⟩ := hB
  exact ⟨.pi e D E, .pi hd he, .pi hsD hsE⟩

theorem Arity.pi_inversion (h : Arity (.pi e A B) c) :
    ∃ a b, c = .arrow a b ∧ Arity A a ∧ Arity B b := by
  obtain ⟨C, hc, hs⟩ := h
  cases hs <;> try (have hh := hc.rigid_head rfl rfl; contradiction)
  case pi hD hE =>
    obtain ⟨_, hd, he⟩ := hc.pi_injective
    exact ⟨_, _, rfl, ⟨_, hd, hD⟩, ⟨_, he, hE⟩⟩

theorem formed_shape (h : IsType Γ A) : ∃ a, Shape A a := by
  induction h using IsType.rec (motive_2 := fun _ _ _ _ => True)
  case u64 => exact ⟨_, .u64⟩
  case i64 => exact ⟨_, .i64⟩
  case array => exact ⟨_, .array⟩
  case lt => exact ⟨_, .lt⟩
  case eq => exact ⟨_, .eq⟩
  case pi hA he hB ihA ihB =>
    obtain ⟨a, ha⟩ := ihA
    obtain ⟨b, hb⟩ := ihB
    exact ⟨_, .pi ha hb⟩
  all_goals trivial

inductive Term where
  | atom
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

/-- Collapse every non-variable/lambda/application constructor to an inert atom.
This deliberately forgets arithmetic, evidence contents, arrays and annotations. -/
def erase : Raw → Term
  | .var x => .var x
  | .lam _ _ body => .lam (erase body)
  | .app f a => .app (erase f) (erase a)
  | _ => .atom

abbrev Context := Nat → Option Ty

def Context.extend (Δ : Context) (a : Ty) : Context
  | 0 => some a
  | n + 1 => Δ n

inductive Typed : Context → Term → Ty → Prop where
  | atom : Typed Δ .atom .base
  | var : Δ x = some a → Typed Δ (.var x) a
  | lam : Typed (Δ.extend a) body b → Typed Δ (.lam body) (.arrow a b)
  | app : Typed Δ f (.arrow a b) → Typed Δ x a → Typed Δ (.app f x) b

/-- Every accessible dependent context entry has the assigned conversion-stable
simple type. No raw context formation is silently assumed. -/
def ContextMatch (Γ : Raw.Context) (Δ : Context) : Prop :=
  ∀ x A, Γ x = some A → ∃ a, Δ x = some a ∧ Arity A a

theorem ContextMatch.extend (h : ContextMatch Γ Δ) (ha : Arity A a) :
    ContextMatch (Γ.extend A) (Δ.extend a) := by
  intro x B hx
  cases x with
  | zero =>
      simp only [Raw.Context.extend, Option.some.injEq] at hx
      subst B
      exact ⟨a, rfl, ha.renaming Nat.succ⟩
  | succ x =>
      simp only [Raw.Context.extend, Option.map_eq_some_iff] at hx
      obtain ⟨C, hC, rfl⟩ := hx
      obtain ⟨c, hc, hs⟩ := h x C hC
      exact ⟨c, hc, hs.renaming Nat.succ⟩

/-- Induction on the unchanged declarative typing derivation, including arbitrary
internal conversions and higher-order arguments. The result type need not itself
be syntactically formed. -/
theorem typed_erasure (h : HasType Γ t A) (hm : ContextMatch Γ Δ) :
    ∃ a, Arity A a ∧ Typed Δ (erase t) a := by
  induction h using HasType.rec
    (motive_1 := fun _ _ _ => True) generalizing Δ
  case u64 | i64 | array | lt | eq | pi => trivial
  case var hx =>
    obtain ⟨a, ha, hs⟩ := hm _ _ hx
    exact ⟨a, hs, .var ha⟩
  case natural => exact ⟨.base, Shape.u64.arity, .atom⟩
  case integer => exact ⟨.base, Shape.i64.arity, .atom⟩
  case uadd => exact ⟨.base, Shape.u64.arity, .atom⟩
  case usub => exact ⟨.base, Shape.u64.arity, .atom⟩
  case elements => exact ⟨.base, Shape.array.arity, .atom⟩
  case decide => exact ⟨.base, Shape.lt.arity, .atom⟩
  case refl => exact ⟨.base, Shape.eq.arity, .atom⟩
  case index => exact ⟨.base, Shape.i64.arity, .atom⟩
  case lam hA he hb ihA ihb =>
    obtain ⟨a, ha⟩ := formed_shape hA
    obtain ⟨b, hb, ht⟩ := ihb (hm.extend ha.arity)
    exact ⟨.arrow a b, ha.arity.pi hb, .lam ht⟩
  case app hf hx ihf ihx =>
    obtain ⟨c, hc, tf⟩ := ihf hm
    obtain ⟨a, b, rfl, hA, hB⟩ := hc.pi_inversion
    obtain ⟨a', hA', tx⟩ := ihx hm
    have he := hA.unique hA'
    subst a'
    exact ⟨b, hB.substitution _, .app tf tx⟩
  case convert ht hc ih =>
    obtain ⟨a, ha, ht⟩ := ih hm
    exact ⟨a, ha.conversion hc, ht⟩

theorem closed_erasure (h : HasType (fun _ => none) t A) :
    ∃ a, Arity A a ∧ Typed (fun _ => none) (erase t) a :=
  typed_erasure h (fun _ _ hx => by cases hx)

theorem typed_at_arity (h : HasType Γ t A) (hm : ContextMatch Γ Δ) (ha : Arity A a) :
    Typed Δ (erase t) a := by
  obtain ⟨b, hb, ht⟩ := typed_erasure h hm
  exact (hb.unique ha) ▸ ht

end Jihoo.CoreBridge.Raw.Beta.SimpleErasure
