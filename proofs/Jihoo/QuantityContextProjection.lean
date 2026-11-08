import Jihoo.QuantityBinderProjection

/-! Structural provenance for quantity descriptors. The immutable syntax view
and contextual domain observer are parameters: their correspondence to Core's
node table and formation/normalization is still a trusted boundary. Descriptors
and owner indices are no longer separate caller inputs to the rooted walk. -/
namespace Jihoo.Quantity.ContextProjection
open Binders

structure RawBinding where
  ty : Nat
  erased : Bool
  deriving DecidableEq, Repr

structure Entry where
  raw : RawBinding
  domain : Domain
  deriving DecidableEq, Repr

def Entry.descriptor (e : Entry) : Binding := ⟨e.raw.erased, e.domain⟩

/-- Only the syntax needed for context entry and variable selection is viewed.
`other` does not authorize projection of the remaining term's execution. -/
inductive Head where
  | lam (erased : Bool) (domain body : Nat)
  | var (index : Nat)
  | lend (owner : Nat)
  | other
  deriving DecidableEq, Repr

abbrev View := Nat → Head
abbrev Observe := List RawBinding → Nat → Option Domain

/-- Contexts are stored oldest first, exactly as Core.infer's append operation.
The observer receives the original annotation and its pre-extension context. -/
def enter (observe : Observe) (ctx : List Entry) (erased : Bool) (ty : Nat) :
    Option (List Entry) := do
  let domain ← observe (ctx.map Entry.raw) ty
  let _ ← classify erased domain
  pure (ctx ++ [⟨⟨ty, erased⟩, domain⟩])

inductive Authentic (observe : Observe) : List Entry → Prop where
  | empty : Authentic observe []
  | push : Authentic observe ctx →
      observe (ctx.map Entry.raw) ty = some domain →
      Permitted erased domain capability →
      Authentic observe (ctx ++ [⟨⟨ty, erased⟩, domain⟩])

theorem enter_origin (h : enter observe ctx erased ty = some next) :
    ∃ domain capability, observe (ctx.map Entry.raw) ty = some domain ∧
      Permitted erased domain capability ∧ next = ctx ++ [⟨⟨ty, erased⟩, domain⟩] := by
  unfold enter at h
  cases ho : observe (ctx.map Entry.raw) ty <;> simp_all
  case some domain =>
    cases hc : classify erased domain <;> simp_all
    exact ⟨_, classify_sound hc⟩

theorem enter_authentic (ha : Authentic observe ctx)
    (h : enter observe ctx erased ty = some next) : Authentic observe next := by
  obtain ⟨_, _, ho, hp, rfl⟩ := enter_origin h
  exact .push ha ho hp

/-- Fuel bounds the original lambda path, including cycles in an untrusted view.
There is no successful partial result when fuel or any observation fails. -/
def walk (view : View) (observe : Observe) : Nat → List Entry → Nat → Option (List Entry × Nat)
  | 0, _, _ => none
  | fuel + 1, ctx, root => match view root with
    | .lam erased ty body => do
        let next ← enter observe ctx erased ty
        walk view observe fuel next body
    | _ => some (ctx, root)

/-- Independent rooted path judgment retains each original node and context. -/
inductive Path (view : View) (observe : Observe) : List Entry → Nat → List Entry → Nat → Prop where
  | stop : (∀ erased ty body, view root ≠ .lam erased ty body) → Path view observe ctx root ctx root
  | step : view root = .lam erased ty body →
      observe (ctx.map Entry.raw) ty = some domain → Permitted erased domain capability →
      Path view observe (ctx ++ [⟨⟨ty, erased⟩, domain⟩]) body final leaf →
      Path view observe ctx root final leaf

theorem walk_sound (h : walk view observe fuel ctx root = some (final, leaf)) :
    Path view observe ctx root final leaf := by
  induction fuel generalizing ctx root with
  | zero => simp [walk] at h
  | succ fuel ih =>
      cases hv : view root with
      | lam erased ty body =>
          simp only [walk, hv] at h
          cases he : enter observe ctx erased ty with
          | none => simp [he] at h
          | some next =>
              simp [he] at h
              obtain ⟨domain, cap, ho, hp, rfl⟩ := enter_origin he
              exact .step hv ho hp (ih h)
      | var k => simp [walk, hv] at h; obtain ⟨rfl, rfl⟩ := h; exact .stop (by simp [hv])
      | lend owner => simp [walk, hv] at h; obtain ⟨rfl, rfl⟩ := h; exact .stop (by simp [hv])
      | other => simp [walk, hv] at h; obtain ⟨rfl, rfl⟩ := h; exact .stop (by simp [hv])

theorem Path.authentic (path : Path view observe ctx root final leaf)
    (ha : Authentic observe ctx) : Authentic observe final := by
  induction path with
  | stop _ => exact ha
  | step _ ho hp _ ih => exact ih (.push ha ho hp)

theorem rooted_authentic (h : walk view observe fuel [] root = some (final, leaf)) :
    Authentic observe final := (walk_sound h).authentic .empty

/-- Core uses ctx[ctx.length - 1 - k], after a bounds check. Quantity event
indices use the same de Bruijn convention, never the forward array position. -/
def lookup (ctx : List Entry) (k : Nat) : Option Entry := ctx.reverse[k]?

theorem lookup_core (h : k < ctx.length) :
    lookup ctx k = ctx[ctx.length - 1 - k]? := by
  simpa [lookup, Nat.sub_sub] using (List.getElem?_reverse (l := ctx) h)

theorem lookup_fresh : lookup (ctx ++ [entry]) 0 = some entry := by
  simp [lookup]

theorem lookup_outer : lookup (ctx ++ [entry]) (k + 1) = lookup ctx k := by
  simp [lookup]

def projectVariableAlias (view : View) (ctx : List Entry) (root : Nat) (body : Control) :
    Option Control := match view root with
  | .var k => projectAlias (ctx.reverse.map Entry.descriptor) k body
  | _ => none

theorem variable_alias_origin
    (h : projectVariableAlias view ctx root body = some projected) :
    ∃ k entry, view root = .var k ∧ lookup ctx k = some entry ∧
      entry.raw.erased = false ∧ (entry.domain = .buffer ∨ entry.domain = .boxedData) ∧
      projected = .alias k body := by
  cases hv : view root <;> simp [projectVariableAlias, hv] at h
  case var k =>
    obtain ⟨binding, hb, he, hd, hp⟩ := projectAlias_origin h
    rw [← List.map_reverse] at hb
    simp only [List.getElem?_map] at hb
    cases hl : ctx.reverse[k]? <;> simp_all [lookup, Entry.descriptor]
    cases hb
    exact ⟨he, hd⟩

/-- Resolve the owner through the original Lend node, without a supplied index.
The reader, result and continuation accounting are not projected here. -/
def projectLendAlias (view : View) (ctx : List Entry) (root : Nat) (body : Control) :
    Option Control := match view root with
  | .lend owner => projectVariableAlias view ctx owner body
  | _ => none

theorem lend_alias_origin
    (h : projectLendAlias view ctx root body = some projected) :
    ∃ owner k entry, view root = .lend owner ∧ view owner = .var k ∧
      lookup ctx k = some entry ∧ entry.raw.erased = false ∧
      (entry.domain = .buffer ∨ entry.domain = .boxedData) ∧ projected = .alias k body := by
  cases hv : view root <;> simp only [projectLendAlias, hv] at h
  all_goals try contradiction
  case lend owner =>
    obtain ⟨k, entry, hk, hl, he, hd, hp⟩ := variable_alias_origin h
    exact ⟨owner, k, entry, rfl, hk, hl, he, hd, hp⟩

/-- Bounded rooted lambda path followed by the exact Lend owner selection. -/
def rootedAlias (view : View) (observe : Observe) (fuel root : Nat) (body : Control) :
    Option Control := do
  let (ctx, leaf) ← walk view observe fuel [] root
  projectLendAlias view ctx leaf body

theorem rooted_alias_origin (h : rootedAlias view observe fuel root body = some projected) :
    ∃ ctx leaf owner k entry, Path view observe [] root ctx leaf ∧ Authentic observe ctx ∧
      view leaf = .lend owner ∧ view owner = .var k ∧ lookup ctx k = some entry ∧
      entry.raw.erased = false ∧ (entry.domain = .buffer ∨ entry.domain = .boxedData) ∧
      projected = .alias k body := by
  unfold rootedAlias at h
  cases hw : walk view observe fuel [] root with
  | none => simp [hw] at h
  | some result =>
    simp only [hw] at h
    obtain ⟨ctx, leaf⟩ := result
    obtain ⟨owner, k, entry, hv, hk, hl, he, hd, hp⟩ := lend_alias_origin h
    exact ⟨ctx, leaf, owner, k, entry, walk_sound hw, rooted_authentic hw, hv, hk, hl, he, hd, hp⟩

theorem rooted_alias_finished (h : rootedAlias view observe fuel root body = some projected)
    (checked : projected.demand r = some n) (run : Finishes body xs) :
    ∃ k, (xs.map (openOwner k)).count r = n := by
  obtain ⟨_, _, _, k, _, _, _, _, _, _, _, _, rfl⟩ := rooted_alias_origin h
  exact ⟨k, alias_finished checked run⟩

theorem rooted_alias_prefix (h : rootedAlias view observe fuel root body = some projected)
    (checked : projected.demand r = some n) (run : Prefix body xs) :
    ∃ k, (xs.map (openOwner k)).count r ≤ n := by
  obtain ⟨_, _, _, k, _, _, _, _, _, _, _, _, rfl⟩ := rooted_alias_origin h
  exact ⟨k, alias_prefix checked run⟩

-- Executable provenance regressions. Each observation is tied to the exact
-- original domain ID and pre-extension context, including erased slots.
private def sampleView : View
  | 0 => .lam false 10 1
  | 1 => .lam true 11 2
  | 2 => .lam false 12 3
  | 3 => .lend 4
  | 4 => .var 2
  | _ => .other

private def sampleObserve (ctx : List RawBinding) (ty : Nat) : Option Domain :=
  if ctx = [] ∧ ty = 10 then some .buffer
  else if ctx = [⟨10, false⟩] ∧ ty = 11 then some .proof
  else if ctx = [⟨10, false⟩, ⟨11, true⟩] ∧ ty = 12 then some .index
  else none

example : rootedAlias sampleView sampleObserve 4 0 (.use 0) = some (.use 2) := by decide
example : rootedAlias sampleView sampleObserve 3 0 (.use 0) = none := by decide
-- The erased middle slot still counts; reversing twice would select U64.
example : rootedAlias (fun n => if n = 4 then .var 0 else sampleView n)
    sampleObserve 4 0 (.use 0) = none := by decide
example : rootedAlias (fun n => if n = 4 then .var 1 else sampleView n)
    sampleObserve 4 0 (.use 0) = none := by decide
example : rootedAlias (fun n => if n = 4 then .var 3 else sampleView n)
    sampleObserve 4 0 (.use 0) = none := by decide
-- Changed original domain ID and erasure cannot reuse the old observations.
example : rootedAlias (fun n => if n = 0 then .lam false 99 1 else sampleView n)
    sampleObserve 4 0 (.use 0) = none := by decide
example : rootedAlias (fun n => if n = 1 then .lam false 11 2 else sampleView n)
    sampleObserve 4 0 (.use 0) = none := by decide
example : rootedAlias (fun n => if n = 0 then .lam false 10 2 else sampleView n)
    sampleObserve 4 0 (.use 0) = none := by decide
example : walk (fun _ => .lam false 10 0) (fun _ _ => some .buffer) 8 [] 0 = none := by decide
example : rootedAlias (fun n => if n = 3 then .lend 99 else sampleView n)
    sampleObserve 4 0 (.use 0) = none := by decide
-- Non-variable owned expressions require a different projection, not a guessed slot.
example : rootedAlias (fun n => if n = 4 then .other else sampleView n)
    sampleObserve 4 0 (.use 0) = none := by decide

private def twoOwners : View
  | 0 => .lam false 10 1
  | 1 => .lam false 10 2
  | 2 => .lend 3
  | 3 => .var 1
  | _ => .other
example : rootedAlias twoOwners (fun _ _ => some .buffer) 3 0 (.use 0) = some (.use 1) := by decide
example : rootedAlias (fun n => if n = 3 then .var 0 else twoOwners n)
    (fun _ _ => some .buffer) 3 0 (.use 0) = some (.use 0) := by decide

end Jihoo.Quantity.ContextProjection
