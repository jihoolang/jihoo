import Jihoo.OwnedCoreApplications

/-! Lexical partition for direct owned-producing applications. The prefix of
capabilities belongs to the producer, while the suffix is retained by the body.
Lexical positions are never deleted: unavailable names become tombstones.
Scalar slots are shared immutable values and are not shifted by an owner binder. -/
namespace Jihoo.OwnedCallContext
open OwnedScalarContext

/-- The argument may use only the allocated capability prefix. -/
def producer (ctx : Context) (limit : Nat) : Context := ctx.map fun b => match b with
  | .owner k => if k < limit then .owner k else .dead
  | other => other

/-- The parameter owns slot zero. Old consumed aliases are dead; old frame
aliases refer to the same suffix identity after the new parameter is prepended. -/
def body (ctx : Context) (limit : Nat) : Context := .owner 0 :: ctx.map fun b => match b with
  | .owner k => if k < limit then .dead else .owner (k - limit + 1)
  | other => other

variable {ctx : Context} {p i k : Nat} {b : Binding}

theorem producer_length : (producer ctx p).length = ctx.length := by simp [producer]

theorem body_length : (body ctx p).length = ctx.length + 1 := by simp [body]

theorem producer_lookup (lookup : ctx[i]? = some b) :
    (producer ctx p)[i]? = some (match b with
      | .owner k => if k < p then .owner k else .dead
      | other => other) := by cases b <;> simp only [producer, List.getElem?_map, lookup, Option.map_some]

theorem body_lookup (lookup : ctx[i]? = some b) :
    (body ctx p)[i+1]? = some (match b with
      | .owner k => if k < p then .dead else .owner (k-p+1)
      | other => other) := by cases b <;> simp only [body, List.getElem?_cons_succ, List.getElem?_map, lookup, Option.map_some]

theorem producer_owned (lookup : ctx[i]? = some (.owner k)) (bound : k < p) :
    (producer ctx p)[i]? = some (.owner k) := by simpa [bound] using producer_lookup (p := p) lookup

theorem producer_frame_dead (lookup : ctx[i]? = some (.owner k)) (bound : p ≤ k) :
    (producer ctx p)[i]? = some .dead := by simpa [show ¬ k < p by omega] using producer_lookup (p := p) lookup

theorem body_consumed_dead (lookup : ctx[i]? = some (.owner k)) (bound : k < p) :
    (body ctx p)[i+1]? = some .dead := by simpa [bound] using body_lookup (p := p) lookup

theorem body_frame (lookup : ctx[i]? = some (.owner k)) (bound : p ≤ k) :
    (body ctx p)[i+1]? = some (.owner (k-p+1)) := by simpa [show ¬ k < p by omega] using body_lookup (p := p) lookup

theorem body_parameter : (body ctx p)[0]? = some (.owner 0) := rfl

theorem producer_scalarBindings : scalarBindings (producer ctx p) values = scalarBindings ctx values := by
  simp only [scalarBindings, ScalarCoreCallers.scalarBindings, producer, List.map_map]
  apply List.map_congr_left
  intro b _
  cases b with
  | owner k => by_cases h : k < p <;> simp [h]
  | scalar | dead => rfl

theorem body_scalarBindings : scalarBindings (body ctx p) values = none :: scalarBindings ctx values := by
  simp only [scalarBindings, ScalarCoreCallers.scalarBindings, body, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  cases b with
  | owner k => by_cases h : k < p <;> simp [h]
  | scalar | dead => rfl

/-- Concrete selected parameter binding; no equality of payloads is involved. -/
theorem body_parameter_identity :
    (LinearCoreCallers.bindings (ownerView (body ctx p)) (returned :: frame))[0]? = some (some returned) := rfl

/-- Retained frame references keep their concrete identity after remapping. -/
theorem frame_identity {owners : List Nat} {k p x returned : Nat} (lookup : owners[k]? = some x) (bound : p ≤ k) :
    (returned :: owners.drop p)[k-p+1]? = some x := by
  simpa [List.getElem?_drop, show p + (k-p) = k by omega] using lookup

/-- Producer references retain their concrete identity inside the prefix. -/
theorem producer_identity {owners : List Nat} {k p x : Nat} (lookup : owners[k]? = some x) (bound : k < p) :
    (owners.take p)[k]? = some x := by simp [bound, lookup]

end Jihoo.OwnedCallContext
