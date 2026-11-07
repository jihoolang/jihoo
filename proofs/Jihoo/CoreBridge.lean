import Jihoo.Semantics

/-! A representation bridge to a selected set of actual core constructor shapes.
It proves scope, weakening and numeric side conditions, not correctness of the
executable checker or a typing translation into the full core. -/
namespace Jihoo.CoreBridge

open Indexed (liftRenaming)

def wordBound : Nat := 2^64
def signedBound : Int := 2^63
abbrev Word := Fin wordBound
abbrev Signed := {n : Int // -signedBound ≤ n ∧ n < signedBound}

/-- Open subtraction has no unchecked encoding. The only subtraction form here
carries a closed non-underflow certificate and a representable upper endpoint. -/
inductive Index where
  | var : Nat → Index
  | lit : Word → Index
  | add : Index → Index → Index
  | closedSub (a b : Nat) (endpoint : a + 1 < wordBound) (bound : b ≤ a) : Index

inductive Ty where
  | u64
  | i64
  | array : Index → Ty
  | lt : Index → Index → Ty
  | eq : Index → Index → Ty
  | pi : Ty → Ty

inductive Term where
  | var : Nat → Term
  | natural : Index → Term
  | integer : Signed → Term
  | elements : List Signed → Term
  | decide (a b : Word) (bound : a.val < b.val) : Term
  | refl : Index → Term
  | zeroLe : Index → Term
  | index : Term → Index → Term → Term
  | lam : Term → Term
  | app : Term → Index → Term
  | letValue : Ty → Term → Term → Term

/-- Trees corresponding to the named constructors of compiler/core.jh.
The implementation instead stores their children as graph-node identifiers. -/
inductive Raw where
  | var : Nat → Raw
  | natural : Nat → Raw
  | integer : Int → Raw
  | u64
  | i64
  | array : Raw → Raw
  | lt : Raw → Raw → Raw
  | eq : Raw → Raw → Raw
  | pi : Bool → Raw → Raw → Raw
  | lam : Bool → Raw → Raw → Raw
  | app : Raw → Raw → Raw
  | elements : List Raw → Raw
  | index : Raw → Raw → Raw → Raw
  | refl : Raw → Raw
  | zeroLe : Raw → Raw
  | decide : Raw → Raw → Raw
  | uadd : Raw → Raw → Raw
  | usub : Raw → Raw → Raw → Raw
  deriving Repr

def Raw.rename (ρ : Nat → Nat) : Raw → Raw
  | .var x => .var (ρ x)
  | .natural n => .natural n
  | .integer n => .integer n
  | .u64 => .u64
  | .i64 => .i64
  | .array n => .array (n.rename ρ)
  | .lt a b => .lt (a.rename ρ) (b.rename ρ)
  | .eq a b => .eq (a.rename ρ) (b.rename ρ)
  | .pi e A B => .pi e (A.rename ρ) (B.rename (liftRenaming ρ))
  | .lam e A body => .lam e (A.rename ρ) (body.rename (liftRenaming ρ))
  | .app f a => .app (f.rename ρ) (a.rename ρ)
  | .elements xs => .elements (xs.map (fun x => x.rename ρ))
  | .index a i p => .index (a.rename ρ) (i.rename ρ) (p.rename ρ)
  | .refl a => .refl (a.rename ρ)
  | .zeroLe a => .zeroLe (a.rename ρ)
  | .decide a b => .decide (a.rename ρ) (b.rename ρ)
  | .uadd a b => .uadd (a.rename ρ) (b.rename ρ)
  | .usub a b p => .usub (a.rename ρ) (b.rename ρ) (p.rename ρ)

def Index.encode (ix : Nat → Nat) : Index → Raw
  | .var n => .var (ix n)
  | .lit n => .natural n.val
  | .add a b => .uadd (a.encode ix) (b.encode ix)
  | .closedSub a b _ _ => .usub (.natural a) (.natural b) (.decide (.natural b) (.natural (a + 1)))

def Ty.encode (ix : Nat → Nat) : Ty → Raw
  | .u64 => .u64
  | .i64 => .i64
  | .array n => .array (n.encode ix)
  | .lt a b => .lt (a.encode ix) (b.encode ix)
  | .eq a b => .eq (a.encode ix) (b.encode ix)
  | .pi B => .pi false .u64 (B.encode (liftRenaming ix))

def Ty.proposition : Ty → Bool
  | .lt _ _ | .eq _ _ => true
  | .pi B => B.proposition
  | _ => false

def Term.encode (ix vx : Nat → Nat) : Term → Raw
  | .var x => .var (vx x)
  | .natural a => a.encode ix
  | .integer n => .integer n.val
  | .elements ns => .elements (ns.map (fun n => .integer n.val))
  | .decide a b _ => .decide (.natural a.val) (.natural b.val)
  | .refl a => .refl (a.encode ix)
  | .zeroLe a => .zeroLe (a.encode ix)
  | .index a i p => .index (a.encode ix vx) (i.encode ix) (p.encode ix vx)
  | .lam body => .lam false .u64 (body.encode (liftRenaming ix) (fun x => vx x + 1))
  | .app f a => .app (f.encode ix vx) (a.encode ix)
  | .letValue A v body =>
      .app (.lam A.proposition (A.encode ix)
        (body.encode (fun x => ix x + 1) (liftRenaming vx))) (v.encode ix vx)

theorem lift_comp (ρ σ : Nat → Nat) :
    (fun x => liftRenaming ρ (liftRenaming σ x)) = liftRenaming (fun x => ρ (σ x)) := by
  funext x
  cases x <;> rfl

theorem lift_shift (ρ σ : Nat → Nat) :
    (fun x => liftRenaming ρ (σ x + 1)) = (fun x => ρ (σ x) + 1) := rfl

theorem Index.encode_rename (t : Index) (ix ρ : Nat → Nat) :
    (t.encode ix).rename ρ = t.encode (fun x => ρ (ix x)) := by
  induction t <;> simp_all [Index.encode, Raw.rename]

theorem Ty.encode_rename (A : Ty) (ix ρ : Nat → Nat) :
    (A.encode ix).rename ρ = A.encode (fun x => ρ (ix x)) := by
  induction A generalizing ix ρ <;>
    simp_all [Ty.encode, Raw.rename, Index.encode_rename, lift_comp]

/-- Translation commutes with unified, capture-avoiding renaming. This includes
weakening, and both annotations and bodies under mixed binder sorts. -/
theorem Term.encode_rename (t : Term) (ix vx ρ : Nat → Nat) :
    (t.encode ix vx).rename ρ = t.encode (fun x => ρ (ix x)) (fun x => ρ (vx x)) := by
  induction t generalizing ix vx ρ <;>
    simp_all [Term.encode, Raw.rename, Index.encode_rename, Ty.encode_rename,
      lift_comp, lift_shift, List.map_map]

def Index.Scoped (n : Nat) : Index → Prop
  | .var x => x < n
  | .lit _ | .closedSub _ _ _ _ => True
  | .add a b => a.Scoped n ∧ b.Scoped n

def Ty.Scoped (n : Nat) : Ty → Prop
  | .u64 | .i64 => True
  | .array a => a.Scoped n
  | .lt a b | .eq a b => a.Scoped n ∧ b.Scoped n
  | .pi B => B.Scoped (n + 1)

def Term.Scoped (n m : Nat) : Term → Prop
  | .var x => x < m
  | .natural a | .refl a | .zeroLe a => a.Scoped n
  | .integer _ | .elements _ | .decide _ _ _ => True
  | .index a i p => a.Scoped n m ∧ i.Scoped n ∧ p.Scoped n m
  | .lam body => body.Scoped (n + 1) m
  | .app f a => f.Scoped n m ∧ a.Scoped n
  | .letValue A v body => A.Scoped n ∧ v.Scoped n m ∧ body.Scoped n (m + 1)

def Raw.Scoped (d : Nat) : Raw → Prop
  | .var x => x < d
  | .natural _ | .integer _ | .u64 | .i64 => True
  | .array n | .refl n | .zeroLe n => n.Scoped d
  | .lt a b | .eq a b | .app a b | .decide a b | .uadd a b => a.Scoped d ∧ b.Scoped d
  | .pi _ A B | .lam _ A B => A.Scoped d ∧ B.Scoped (d + 1)
  | .elements xs => ∀ x ∈ xs, x.Scoped d
  | .index a b c | .usub a b c => a.Scoped d ∧ b.Scoped d ∧ c.Scoped d

abbrev Within (n d : Nat) (ρ : Nat → Nat) := ∀ x, x < n → ρ x < d

theorem within_lift (h : Within n d ρ) : Within (n + 1) (d + 1) (liftRenaming ρ) := by
  intro x hx
  cases x with
  | zero => simp [liftRenaming]
  | succ x => have := h x (by omega); simp only [liftRenaming]; omega

theorem within_shift (h : Within n d ρ) : Within n (d + 1) (fun x => ρ x + 1) := by
  intro x hx
  have := h x hx
  change ρ x + 1 < d + 1
  omega

theorem Index.encode_scoped {t : Index} (h : t.Scoped n) (hi : Within n d ix) :
    (t.encode ix).Scoped d := by
  induction t <;> simp only [Index.encode, Raw.Scoped] at *
  case var x => exact hi x h
  case add a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  case closedSub => exact ⟨trivial, trivial, trivial, trivial⟩

theorem Ty.encode_scoped {A : Ty} (h : A.Scoped n) (hi : Within n d ix) :
    (A.encode ix).Scoped d := by
  induction A generalizing n d ix <;> simp only [Ty.encode, Raw.Scoped] at *
  case array => exact Index.encode_scoped h hi
  case lt => exact ⟨Index.encode_scoped h.1 hi, Index.encode_scoped h.2 hi⟩
  case eq => exact ⟨Index.encode_scoped h.1 hi, Index.encode_scoped h.2 hi⟩
  case pi B ih => exact ⟨trivial, ih h (within_lift hi)⟩

/-- Source finite scope is translated to the single unified target scope. -/
theorem Term.encode_scoped {t : Term} (h : t.Scoped n m)
    (hi : Within n d ix) (hv : Within m d vx) : (t.encode ix vx).Scoped d := by
  induction t generalizing n m d ix vx <;> simp only [Term.encode, Raw.Scoped] at *
  case var x => exact hv x h
  case natural => exact Index.encode_scoped h hi
  case elements ns =>
    intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    simp [Raw.Scoped]
  case decide => exact ⟨trivial, trivial⟩
  case refl => exact Index.encode_scoped h hi
  case zeroLe => exact Index.encode_scoped h hi
  case index a i p iha ihp => exact ⟨iha h.1 hi hv, Index.encode_scoped h.2.1 hi, ihp h.2.2 hi hv⟩
  case lam body ih => exact ⟨trivial, ih h (within_lift hi) (within_shift hv)⟩
  case app f a ih => exact ⟨ih h.1 hi hv, Index.encode_scoped h.2 hi⟩
  case letValue A v body ihv ihb =>
      exact ⟨⟨Ty.encode_scoped h.1 hi, ihb h.2.2 (within_shift hi) (within_lift hv)⟩,
        ihv h.2.1 hi hv⟩

end Jihoo.CoreBridge
