import Jihoo.SizedBufferHeap
import Jihoo.DependentBufferIndices
import Jihoo.LinearCoreCallers

namespace Jihoo.SizedBufferContext
open LinearHeapPrograms
abbrev Indices := DependentBufferIndices.Expr

inductive Entry where
  | nat (n : Nat)
  | scalar
  | owner (slot : Nat)
  | bound (fact : DependentBufferIndices.BoundFact)
  | dead

inductive Value where
  | nat (n : Nat)
  | scalar (v : Nat)
  | owner (x : Nat)
  | borrow (x : Nat)
  | ghost
  deriving DecidableEq, Repr
abbrev Context := List Entry
abbrev Env := List Value

def naturalEnv (ctx : Context) : DependentBufferIndices.Env := fun k =>
  match ctx[k]? with | some (.nat n) => some n | _ => none

def runtimeNats (env : Env) : DependentBufferIndices.Env := fun k =>
  match env[k]? with | some (.nat n) => some n | _ => none

def proofs (ctx : Context) : DependentBufferIndices.ProofEnv := fun k =>
  match ctx[k]? with | some (.bound fact) => some fact | _ => none

def fresh (ctx : Context) : Context := .owner 0 :: ctx.map fun b => match b with
  | .owner k => .owner (k+1) | other => other

def consumed (slot : Nat) (ctx : Context) : Context := ctx.map fun b => match b with
  | .owner k => if k = slot then .dead else .owner (if slot < k then k-1 else k)
  | other => other

def bindNat (n : Nat) (ctx : Context) : Context := .nat n :: ctx

def scalarReturned (ctx : Context) (slot : Nat) : Context := .owner slot :: .scalar :: ctx

def ValidNats (ctx : Context) : Prop := DependentBufferIndices.ValidEnv (naturalEnv ctx)

structure Agrees (ctx : Context) (owners : List Nat) (env : Env) : Prop where
  nat_lookup : ∀ (k n : Nat), ctx[k]? = some (.nat n) → env[k]? = some (.nat n)
  scalar_lookup : ∀ (k : Nat), ctx[k]? = some .scalar → ∃ v, env[k]? = some (.scalar v)
  owner_lookup : ∀ (k slot : Nat), ctx[k]? = some (.owner slot) →
    ∃ x, owners[slot]? = some x ∧ env[k]? = some (.owner x)
  bound_lookup : ∀ (k : Nat) (fact : DependentBufferIndices.BoundFact), ctx[k]? = some (.bound fact) → env[k]? = some .ghost

structure Layout (s : SizedBufferHeap.State) (owners sizes : List Nat) : Prop where
  length : owners.length = sizes.length
  lookup : ∀ (k x n : Nat), owners[k]? = some x → sizes[k]? = some n → s.length x = n



variable {ctx : Context} {owners : List Nat} {env : Env}

theorem Agrees.prepend (h : Agrees ctx owners env) {entry : Entry} {value : Value}
    (hn : ∀ n, entry = .nat n → value = .nat n)
    (hs : entry = .scalar → ∃ v, value = .scalar v)
    (ho : ∀ k, entry = .owner k → ∃ x, owners[k]? = some x ∧ value = .owner x)
    (hb : ∀ f, entry = .bound f → value = .ghost) :
    Agrees (entry :: ctx) owners (value :: env) := by
  constructor
  · intro k n lookup; cases k with
    | zero => simpa using congrArg some (hn n (Option.some.inj lookup))
    | succ k => exact h.nat_lookup k n lookup
  · intro k lookup; cases k with
    | zero => obtain ⟨v, hv⟩ := hs (Option.some.inj lookup); exact ⟨v, congrArg some hv⟩
    | succ k => exact h.scalar_lookup k lookup
  · intro k slot lookup; cases k with
    | zero => obtain ⟨x,hx,hv⟩ := ho slot (Option.some.inj lookup); exact ⟨x,hx,congrArg some hv⟩
    | succ k => exact h.owner_lookup k slot lookup
  · intro k f lookup; cases k with
    | zero => exact congrArg some (hb f (Option.some.inj lookup))
    | succ k => exact h.bound_lookup k f lookup

theorem Agrees.dead (h : Agrees ctx owners env) :
    Agrees (.dead :: ctx) owners (value :: env) := by
  apply h.prepend <;> intros <;> contradiction

theorem Agrees.bound (h : Agrees ctx owners env) :
    Agrees (.bound fact :: ctx) owners (.ghost :: env) := by
  apply h.prepend <;> intros <;> first | contradiction | rfl

theorem Agrees.bindNat (h : Agrees ctx owners env) :
    Agrees (bindNat n ctx) owners (.nat n :: env) := by
  apply h.prepend
  · intro m eq; cases eq; rfl
  all_goals intros; contradiction

theorem Agrees.scalarReturned (h : Agrees ctx owners env)
    (selected : Select owners slot x rest) :
    Agrees (scalarReturned ctx slot) owners (.owner x :: .scalar v :: env) := by
  apply Agrees.prepend
  · apply h.prepend
    · intros; contradiction
    · intro _; exact ⟨v,rfl⟩
    · intros; contradiction
    · intros; contradiction
  · intros; contradiction
  · intros; contradiction
  · intro k eq; cases eq; exact ⟨x, LinearCoreCallers.Select.lookup_selected selected, rfl⟩
  · intros; contradiction

theorem Agrees.fresh (h : Agrees ctx owners env) :
    Agrees (fresh ctx) (x :: owners) (.owner x :: env) := by
  apply Agrees.prepend
  · constructor
    · intro k n lookup
      cases old : ctx[k]? with
      | none => simp [List.getElem?_map, old] at lookup
      | some b => cases b <;> simp [List.getElem?_map, old] at lookup
                  case nat n' => subst n'; exact h.nat_lookup k n old
    · intro k lookup
      cases old : ctx[k]? with
      | none => simp [List.getElem?_map, old] at lookup
      | some b => cases b <;> simp [List.getElem?_map, old] at lookup
                  case scalar => exact h.scalar_lookup k old
    · intro k slot lookup
      cases old : ctx[k]? with
      | none => simp [List.getElem?_map, old] at lookup
      | some b => cases b <;> simp [List.getElem?_map, old] at lookup
                  case owner j => subst slot; obtain ⟨y,hy,he⟩ := h.owner_lookup k j old; exact ⟨y,hy,he⟩
    · intro k f lookup
      cases old : ctx[k]? with
      | none => simp [List.getElem?_map, old] at lookup
      | some b => cases b <;> simp [List.getElem?_map, old] at lookup
                  case bound f' => subst f'; exact h.bound_lookup k f old
  · intros; contradiction
  · intros; contradiction
  · intro k eq; cases eq; exact ⟨x,rfl,rfl⟩
  · intros; contradiction



theorem Agrees.consumed (h : Agrees ctx owners env) (selected : Select owners slot x rest) :
    Agrees (consumed slot ctx) rest env := by
  constructor
  · intro k n lookup
    cases old : ctx[k]? with
    | none => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
    | some b =>
      cases b with
      | nat z =>
        simp only [SizedBufferContext.consumed, List.getElem?_map, old, Option.map_some, Option.some.injEq] at lookup
        cases lookup
        exact h.nat_lookup k n old
      | scalar  => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
      | owner z =>
        by_cases eq : z = slot
        · simp [SizedBufferContext.consumed, List.getElem?_map, old, eq] at lookup
        · simp only [SizedBufferContext.consumed, List.getElem?_map, old, Option.map_some, ite_eq_right eq, Option.some.injEq] at lookup
          contradiction
      | bound z => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
      | dead  => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
  · intro k lookup
    cases old : ctx[k]? with
    | none => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
    | some b =>
      cases b with
      | nat z => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
      | scalar  =>
        simp only [SizedBufferContext.consumed, List.getElem?_map, old, Option.map_some] at lookup
        exact h.scalar_lookup k old
      | owner z =>
        by_cases eq : z = slot
        · simp [SizedBufferContext.consumed, List.getElem?_map, old, eq] at lookup
        · simp only [SizedBufferContext.consumed, List.getElem?_map, old, Option.map_some, ite_eq_right eq, Option.some.injEq] at lookup
          contradiction
      | bound z => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
      | dead  => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
  · intro k j lookup
    cases old : ctx[k]? with
    | none => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
    | some b =>
      cases b with
      | nat z => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
      | scalar  => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
      | owner z =>
        by_cases eq : z = slot
        · simp [SizedBufferContext.consumed, List.getElem?_map, old, eq] at lookup
        · simp only [SizedBufferContext.consumed, List.getElem?_map, old, Option.map_some, ite_eq_right eq, Option.some.injEq] at lookup
          cases lookup
          obtain ⟨y, hy, he⟩ := h.owner_lookup k z old
          exact ⟨y, (LinearCoreCallers.Select.lookup_other selected eq).trans hy, he⟩
      | bound z => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
      | dead  => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
  · intro k f lookup
    cases old : ctx[k]? with
    | none => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
    | some b =>
      cases b with
      | nat z => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
      | scalar  => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup
      | owner z =>
        by_cases eq : z = slot
        · simp [SizedBufferContext.consumed, List.getElem?_map, old, eq] at lookup
        · simp only [SizedBufferContext.consumed, List.getElem?_map, old, Option.map_some, ite_eq_right eq, Option.some.injEq] at lookup
          contradiction
      | bound z =>
        simp only [SizedBufferContext.consumed, List.getElem?_map, old, Option.map_some, Option.some.injEq] at lookup
        cases lookup
        exact h.bound_lookup k f old
      | dead  => simp [SizedBufferContext.consumed, List.getElem?_map, old] at lookup

theorem Agrees.nats_transport (h : Agrees ctx owners env)
    (lookup : naturalEnv ctx k = some n) : runtimeNats env k = some n := by
  cases old : ctx[k]? with
  | none => simp [naturalEnv, old] at lookup
  | some b =>
    cases b <;> simp [naturalEnv, old] at lookup
    case nat m => subst m; simp [runtimeNats, h.nat_lookup k n old]

theorem Layout.owner_result (h : Layout s owners [n]) (lookup : owners[0]? = some x) :
    owners = [x] ∧ s.length x = n := by
  have len := h.length
  cases owners with
  | nil => simp at lookup
  | cons y ys =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
    subst y
    have empty : ys = [] := by simpa using len
    subst ys
    exact ⟨rfl, h.lookup 0 x n rfl rfl⟩



theorem Layout.allocate (h : Layout s owners sizes) (valid : SizedBufferHeap.Valid s)
    (owned : Owns s.heap owners) :
    Layout (SizedBufferHeap.allocate s n v) (s.heap.nextObject :: owners) (n :: sizes) := by
  constructor
  · simpa using h.length
  · intro k x m hx hm
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hm
              subst x; subst m; exact SizedBufferHeap.allocation_length
    | succ k =>
      have old := valid.allocated x (owned.live x (List.mem_of_getElem? hx))
      have ne : x ≠ s.heap.nextObject := by omega
      simpa [SizedBufferHeap.allocate, HeapLeases.put, ne] using h.lookup k x m hx hm

theorem Layout.select (h : Layout s owners sizes) (selected : Select owners slot x rest) :
    Layout s rest (sizes.eraseIdx slot) := by
  induction selected generalizing sizes with
  | here =>
    cases sizes with
    | nil => have bad := h.length; simp at bad
    | cons n ns =>
      constructor
      · simpa using h.length
      · intro k y m hy hm; exact h.lookup (k+1) y m hy hm
  | there selected ih =>
    cases sizes with
    | nil => have := h.length; simp at this
    | cons n ns =>
      have tail : Layout s _ ns := ⟨by simpa using h.length,
        by intro k y m hy hm; exact h.lookup (k+1) y m hy hm⟩
      have next := ih tail
      constructor
      · simpa using next.length
      · intro k y m hy hm
        cases k with
        | zero => exact h.lookup 0 y m hy hm
        | succ k => exact next.lookup k y m hy hm

theorem Layout.consumed (h : Layout s owners sizes) (selected : Select owners slot x rest) :
    Layout (SizedBufferHeap.release s x) rest (sizes.eraseIdx slot) :=
  ⟨(h.select selected).length, (h.select selected).lookup⟩

theorem Layout.restored (h : Layout s owners sizes) :
    Layout (SizedBufferHeap.restore s) owners sizes := ⟨h.length, h.lookup⟩

end Jihoo.SizedBufferContext
