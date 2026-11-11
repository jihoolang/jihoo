import Jihoo.SizedBufferContext

/-! Lexical capability partitions preserve natural parameters and erased bounds.
Only owner authority changes; runtime lexical environments keep old aliases. -/
namespace Jihoo.SizedBufferContext
open LinearHeapPrograms

def mapOwners (f : Nat → Option Nat) (ctx : Context) : Context := ctx.map fun e =>
  match e with
  | .owner k => match f k with | some j => .owner j | none => .dead
  | other => other

def producer (ctx : Context) (p : Nat) : Context :=
  mapOwners (fun k => if k < p then some k else none) ctx

def callBody (ctx : Context) (p : Nat) : Context :=
  .owner 0 :: mapOwners (fun k => if k < p then none else some (k-p+1)) ctx

def transferred (ctx : Context) (slot : Nat) : Context :=
  .owner slot :: mapOwners (fun k => if k = slot then none else some k) ctx

def ownedReturned (ctx : Context) (slot : Nat) : Context :=
  .owner (slot+1) :: fresh ctx

theorem mapOwners_naturalEnv : naturalEnv (mapOwners f ctx) = naturalEnv ctx := by
  funext k
  simp only [naturalEnv, mapOwners, List.getElem?_map]
  cases h : ctx[k]? with
  | none => rfl
  | some e => cases e <;> simp only [Option.map_some]
              case owner j => cases f j <;> rfl
              all_goals rfl

theorem mapOwners_proofs : proofs (mapOwners f ctx) = proofs ctx := by
  funext k
  simp only [proofs, mapOwners, List.getElem?_map]
  cases h : ctx[k]? with
  | none => rfl
  | some e => cases e <;> simp only [Option.map_some]
              case owner j => cases f j <;> rfl
              all_goals rfl

theorem Agrees.mapOwners (h : Agrees ctx owners env)
    (transport : ∀ k j x, f k = some j → owners[k]? = some x → next[j]? = some x) :
    Agrees (mapOwners f ctx) next env := by
  constructor
  · intro k n lookup
    cases old : ctx[k]? with
    | none => simp [SizedBufferContext.mapOwners, List.getElem?_map, old] at lookup
    | some e =>
      cases e <;> simp only [SizedBufferContext.mapOwners, List.getElem?_map, old, Option.map_some] at lookup
      case nat m => cases lookup; exact h.nat_lookup k n old
      case owner j => cases mapped : f j <;> simp [mapped] at lookup
      all_goals cases lookup
  · intro k lookup
    cases old : ctx[k]? with
    | none => simp [SizedBufferContext.mapOwners, List.getElem?_map, old] at lookup
    | some e =>
      cases e <;> simp only [SizedBufferContext.mapOwners, List.getElem?_map, old, Option.map_some] at lookup
      case scalar => exact h.scalar_lookup k old
      case owner j => cases mapped : f j <;> simp [mapped] at lookup
      all_goals cases lookup
  · intro k j lookup
    cases old : ctx[k]? with
    | none => simp [SizedBufferContext.mapOwners, List.getElem?_map, old] at lookup
    | some e =>
      cases e <;> simp only [SizedBufferContext.mapOwners, List.getElem?_map, old, Option.map_some] at lookup
      case owner l =>
        cases mapped : f l with
        | none => simp [mapped] at lookup
        | some z =>
          simp only [mapped, Option.some.injEq, Entry.owner.injEq] at lookup
          subst z
          obtain ⟨x, hx, he⟩ := h.owner_lookup k l old
          exact ⟨x, transport l j x mapped hx, he⟩
      all_goals cases lookup
  · intro k fact lookup
    cases old : ctx[k]? with
    | none => simp [SizedBufferContext.mapOwners, List.getElem?_map, old] at lookup
    | some e =>
      cases e <;> simp only [SizedBufferContext.mapOwners, List.getElem?_map, old, Option.map_some] at lookup
      case bound b => cases lookup; exact h.bound_lookup k fact old
      case owner j => cases mapped : f j <;> simp [mapped] at lookup
      all_goals cases lookup

theorem Agrees.producer (h : Agrees ctx owners env) :
    Agrees (producer ctx p) (owners.take p) env := by
  apply h.mapOwners
  intro k j x eq lookup
  by_cases bound : k < p
  · simp only [bound, ite_true, Option.some.injEq] at eq
    subst j
    simpa [bound] using lookup
  · simp [bound] at eq

theorem Agrees.body (h : Agrees ctx owners env) :
    Agrees (callBody ctx p) (returned :: owners.drop p) (.owner returned :: env) := by
  apply Agrees.prepend
  · apply h.mapOwners
    intro k j x eq lookup
    by_cases bound : k < p
    · simp [bound] at eq
    · simp only [bound, ite_false, Option.some.injEq] at eq
      subst j
      simpa [List.getElem?_drop, show p + (k-p) = k by omega] using lookup
  · intros; contradiction
  · intros; contradiction
  · intro k eq; cases eq; exact ⟨returned, rfl, rfl⟩
  · intros; contradiction

theorem Agrees.transferred (h : Agrees ctx owners env) (lookup : owners[slot]? = some x) :
    Agrees (transferred ctx slot) owners (.owner x :: env) := by
  apply Agrees.prepend
  · apply h.mapOwners
    intro k j y eq old
    by_cases same : k = slot
    · simp [same] at eq
    · simp only [same, ite_false, Option.some.injEq] at eq
      subst j; exact old
  · intros; contradiction
  · intros; contradiction
  · intro k eq; cases eq; exact ⟨x, lookup, rfl⟩
  · intros; contradiction

theorem Agrees.ownedReturned (h : Agrees ctx owners env) (lookup : owners[slot]? = some x) :
    Agrees (ownedReturned ctx slot) (newOwner :: owners) (.owner x :: .owner newOwner :: env) := by
  apply Agrees.prepend h.fresh
  · intros; contradiction
  · intros; contradiction
  · intro k eq; cases eq; exact ⟨x, lookup, rfl⟩
  · intros; contradiction

theorem Layout.take (h : Layout s owners sizes) :
    Layout s (owners.take p) (sizes.take p) := by
  constructor
  · simp [h.length]
  · intro k x n hx hn
    by_cases bound : k < p
    · exact h.lookup k x n (by simpa [bound] using hx) (by simpa [bound] using hn)
    · simp [List.getElem?_take, bound] at hx

theorem Layout.drop (h : Layout s owners sizes) :
    Layout s (owners.drop p) (sizes.drop p) := by
  constructor
  · simp [h.length]
  · intro k x n hx hn
    exact h.lookup (p+k) x n (by simpa [List.getElem?_drop] using hx)
      (by simpa [List.getElem?_drop] using hn)

theorem Layout.cons (h : Layout s owners sizes) (length : s.length x = n) :
    Layout s (x :: owners) (n :: sizes) := by
  constructor
  · simp [h.length]
  · intro k y m hy hm
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hy hm
              subst y; subst m; exact length
    | succ k => exact h.lookup k y m hy hm

theorem Layout.steps_preserved (h : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : SizedBufferHeap.Steps s es t) : Layout t owners sizes := by
  refine ⟨h.length, ?_⟩
  intro k x n hx hn
  rw [(SizedBufferHeap.lengths_preserved (valid.allocated x (owned.live x (List.mem_of_getElem? hx))) run).2]
  exact h.lookup k x n hx hn

theorem Layout.recombine (h : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : SizedBufferHeap.Steps s es t) (length : t.length returned = n) :
    Layout t (returned :: owners.drop p) (n :: sizes.drop p) :=
  ((h.steps_preserved valid owned run).drop).cons length

end Jihoo.SizedBufferContext
