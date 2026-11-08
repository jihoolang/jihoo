import Jihoo.QuantityControl

/-! Scope-preserving identification of variable slots with resource identities.
The map may be non-injective. Its authenticity (which slots denote the same
physical owner) must come from a future typing/lend projection, not this module.
This is renaming of use events, not substitution of effectful expressions. -/
namespace Jihoo.Quantity

/-- A fresh local slot never aliases an outer resource. -/
def lift (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def Control.rename (ρ : Nat → Nat) : Control → Control
  | .pure => .pure
  | .trap => .trap
  | .use x => .use (ρ x)
  | .seq a b => .seq (a.rename ρ) (b.rename ρ)
  | .branch a b => .branch (a.rename ρ) (b.rename ρ)
  | .repeat b => .repeat (b.rename ρ)
  | .once b => .once (b.rename ρ)
  | .closure b => .closure (b.rename ρ)
  | .erased b => .erased (b.rename ρ)
  | .scope mode b => .scope mode (b.rename (lift ρ))

theorem lift_id : lift id = id := by funext n; cases n <;> rfl

theorem lift_comp : lift (σ ∘ ρ) = lift σ ∘ lift ρ := by
  funext n; cases n <;> rfl

theorem Control.rename_id (c : Control) : c.rename id = c := by
  induction c <;> simp_all [rename, lift_id]

theorem Control.rename_comp (c : Control) :
    (c.rename ρ).rename σ = c.rename (σ ∘ ρ) := by
  induction c generalizing ρ σ <;> simp_all [rename, lift_comp]

theorem discharge_map (xs : List Nat) :
    discharge (xs.map (lift ρ)) = (discharge xs).map ρ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [discharge, lift, ih]

/-- Execution renaming permits owner-slot identification, not only bijections.
Crucially, branch selection happens after the same renaming of both alternatives. -/
theorem Finishes.rename (run : Finishes c xs) (ρ : Nat → Nat) :
    Finishes (c.rename ρ) (xs.map ρ) := by
  induction run generalizing ρ with
  | pure => exact .pure
  | use => exact .use
  | seq ha hb iha ihb => simpa only [Control.rename, List.map_append] using Finishes.seq (iha ρ) (ihb ρ)
  | left ha ih => exact .left (ih ρ)
  | right hb ih => exact .right (ih ρ)
  | repeatZero => exact .repeatZero
  | repeatNext ha hb iha ihb => simpa only [Control.rename, List.map_append] using Finishes.repeatNext (iha ρ) (ihb ρ)
  | once ha ih => exact .once (ih ρ)
  | closure => exact .closure
  | erased => exact .erased
  | bind ha ih => simpa only [Control.rename, discharge_map] using Finishes.bind (ih (lift ρ))

theorem Prefix.rename (run : Prefix c xs) (ρ : Nat → Nat) :
    Prefix (c.rename ρ) (xs.map ρ) := by
  induction run generalizing ρ with
  | start => exact .start
  | use => exact .use
  | seqLeft ha ih => exact .seqLeft (ih ρ)
  | seqRight ha hb ih => simpa only [Control.rename, List.map_append] using Prefix.seqRight (ha.rename ρ) (ih ρ)
  | left ha ih => exact .left (ih ρ)
  | right ha ih => exact .right (ih ρ)
  | repeatNext ha hb ih => simpa only [Control.rename, List.map_append] using Prefix.repeatNext (ha.rename ρ) (ih ρ)
  | repeatBody ha ih => exact .repeatBody (ih ρ)
  | once ha ih => exact .once (ih ρ)
  | bind ha ih => simpa only [Control.rename, discharge_map] using Prefix.bind (ih (lift ρ))

/-- Test demands after slot identification. Summing separately checked slot
counts would wrongly reject alternate branches using two names of one owner. -/
def AliasLinear (ρ : Nat → Nat) (owners : List Nat) (c : Control) : Prop :=
  Linear owners (c.rename ρ)

theorem AliasLinear.finished (h : AliasLinear ρ owners c) (run : Finishes c xs) :
    ∀ owner ∈ owners, (xs.map ρ).count owner = 1 := Linear.finished h (run.rename ρ)

theorem AliasLinear.prefix (h : AliasLinear ρ owners c) (run : Prefix c xs) :
    ∀ owner ∈ owners, (xs.map ρ).count owner ≤ 1 := Linear.prefix h (run.rename ρ)

/-- Open a returned-owner slot by identifying it with an existing outer owner.
Outer slots shift down, unlike entry to a fresh linear scope. -/
def openOwner (owner : Nat) : Nat → Nat
  | 0 => owner
  | n + 1 => n

/-- Opening an alias aggregates the returned slot with the chosen original
slot; it neither drops that use nor counts two independent owned resources. -/
theorem openOwner_count (xs : List Nat) :
    (xs.map (openOwner owner)).count r =
      xs.count (r + 1) + (if owner = r then xs.count 0 else 0) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases x with
      | zero => by_cases h : owner = r <;>
          (simp_all [openOwner] <;> omega)
      | succ x => by_cases h : owner = r <;> by_cases hx : x = r <;>
          (simp_all [openOwner] <;> omega)

abbrev Control.alias (owner : Nat) (body : Control) : Control :=
  body.rename (openOwner owner)

theorem alias_finished (h : (Control.alias owner body).demand r = some n)
    (run : Finishes body xs) : (xs.map (openOwner owner)).count r = n :=
  (run.rename _).count_eq h

theorem alias_prefix (h : (Control.alias owner body).demand r = some n)
    (run : Prefix body xs) : (xs.map (openOwner owner)).count r ≤ n :=
  (run.rename _).count_le h

end Jihoo.Quantity
