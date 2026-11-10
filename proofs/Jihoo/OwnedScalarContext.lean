import Jihoo.OwnedLendContext
import Jihoo.ScalarCoreCallers

/-! Mixed scalar/owner lexical contexts for the same direct Core ownership
rules. Direct Free adds no binder. Scalar Lend adds a scalar binding without
allocating an owner; owned Lend adds an owner without shifting scalar slots. -/
namespace Jihoo.OwnedScalarContext
open HeapLeases ScopedLend LinearHeapPrograms
abbrev Binding := ScalarCoreCallers.Binding
abbrev Context := ScalarCoreCallers.Context
abbrev Result := ScalarCoreCallers.Result
abbrev resultAt := ScalarCoreCallers.resultAt
abbrev ownerSlot := ScalarCoreCallers.ownerSlot
abbrev ownerView := ScalarCoreCallers.ownerView
abbrev scalarBindings := ScalarCoreCallers.scalarBindings
abbrev fresh := ScalarCoreCallers.fresh

def consumed (slot : Nat) (ctx : Context) : Context := ctx.map fun b => match b with
  | .owner k => if k = slot then .dead else .owner (if slot < k then k - 1 else k)
  | other => other

def ownedReturned (ctx : Context) (slot : Nat) : Context := .owner (slot + 1) :: fresh ctx

def scalarShift (ctx : Context) : Context := ctx.map fun b => match b with
  | .scalar k => .scalar (k + 1)
  | other => other

def scalarReturned (ctx : Context) (slot : Nat) : Context :=
  .owner slot :: .scalar 0 :: scalarShift ctx

def readerRoles (ctx : Context) (slot : Nat) : List Graph.Role :=
  OwnedLendContext.readerRoles (ownerView ctx) slot

theorem fresh_ownerView : ownerView (fresh ctx) = LinearCoreCallers.fresh (ownerView ctx) := by
  simp only [ownerView, fresh, ScalarCoreCallers.ownerView, ScalarCoreCallers.fresh,
    LinearCoreCallers.fresh, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

theorem consumed_ownerView :
    ownerView (consumed slot ctx) = LinearCoreCallers.consumed slot (ownerView ctx) := by
  simp only [ownerView, ScalarCoreCallers.ownerView, consumed,
    LinearCoreCallers.consumed, List.map_map]
  apply List.map_congr_left
  intro b _
  cases b with
  | owner k => by_cases eq : k = slot <;> simp [eq]
  | scalar | dead => rfl

theorem ownedReturned_ownerView : ownerView (ownedReturned ctx slot) =
    OwnedLendContext.returnedContext (ownerView ctx) slot := by
  change some (slot + 1) :: ownerView (fresh ctx) = _
  rw [fresh_ownerView]
  rfl

theorem scalarShift_ownerView : ownerView (scalarShift ctx) = ownerView ctx := by
  simp only [ownerView, ScalarCoreCallers.ownerView, scalarShift, List.map_map]
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

theorem scalarReturned_ownerView : ownerView (scalarReturned ctx slot) =
    some slot :: none :: ownerView ctx := by
  change some slot :: none :: ownerView (scalarShift ctx) = _
  rw [scalarShift_ownerView]

theorem consumed_scalarBindings : scalarBindings (consumed slot ctx) values = scalarBindings ctx values := by
  simp only [scalarBindings, ScalarCoreCallers.scalarBindings, consumed, List.map_map]
  apply List.map_congr_left
  intro b _
  cases b with
  | owner k => by_cases eq : k = slot <;> simp [eq]
  | scalar | dead => rfl

theorem fresh_scalarBindings : scalarBindings (fresh ctx) values = none :: scalarBindings ctx values :=
  ScalarCoreCallers.fresh_scalarBindings

theorem ownedReturned_scalarBindings : scalarBindings (ownedReturned ctx slot) values =
    none :: none :: scalarBindings ctx values := by
  change none :: scalarBindings (fresh ctx) values = _
  rw [fresh_scalarBindings]

theorem scalarShift_scalarBindings : scalarBindings (scalarShift ctx) (v :: values) =
    scalarBindings ctx values := by
  simp only [scalarBindings, ScalarCoreCallers.scalarBindings, scalarShift, List.map_map]
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

theorem scalarReturned_scalarBindings : scalarBindings (scalarReturned ctx slot) (v :: values) =
    none :: some v :: scalarBindings ctx values := by
  change none :: some v :: scalarBindings (scalarShift ctx) (v :: values) = _
  rw [scalarShift_scalarBindings]

theorem scalarReturned_ownerBindings (selected : LinearHeapPrograms.Select owners slot x rest) :
    LinearCoreCallers.bindings (ownerView (scalarReturned ctx slot)) owners =
      some x :: none :: LinearCoreCallers.bindings (ownerView ctx) owners := by
  rw [scalarReturned_ownerView]
  simp [LinearCoreCallers.bindings, LinearCoreCallers.Select.lookup_selected selected]

theorem ownedReturned_ownerBindings (selected : LinearHeapPrograms.Select owners slot x rest) :
    LinearCoreCallers.bindings (ownerView (ownedReturned ctx slot)) (newOwner :: owners) =
      some x :: some newOwner :: LinearCoreCallers.bindings (ownerView ctx) owners := by
  rw [ownedReturned_ownerView]
  exact OwnedLendContext.returned_bindings selected

inductive ScalarShape (g : Graph.Graph) (root owner init rest : Nat) : Prop where
  | intro (reader cont refTy resultTy inner ownerTy : Nat) :
      Graph.nodeAt g root = .lend owner reader cont →
      Graph.nodeAt g reader = .lam false refTy init → Graph.refOne g refTy = true →
      Graph.nodeAt g cont = .lam false resultTy inner → Graph.nodeAt g resultTy = .i64 →
      Graph.nodeAt g inner = .lam false ownerTy rest → Graph.bufferOne g ownerTy = true →
      ScalarShape g root owner init rest

theorem ScalarShape.head (h : ScalarShape g root owner init rest) :
    ∃ reader cont, Graph.nodeAt g root = .lend owner reader cont := by
  cases h with
  | intro reader cont _ _ _ _ head _ _ _ _ _ _ => exact ⟨reader, cont, head⟩

theorem ScalarShape.unique (a : ScalarShape g root owner init rest)
    (b : ScalarShape g root owner' init' rest') : owner = owner' ∧ init = init' ∧ rest = rest' := by
  cases a with
  | intro reader cont refTy resultTy inner ownerTy h hr _ hc _ hi _ =>
    cases b with
    | intro reader' cont' refTy' resultTy' inner' ownerTy' h' hr' _ hc' _ hi' _ =>
      have eq := h.symm.trans h'; cases eq
      have eq := hr.symm.trans hr'; cases eq
      have eq := hc.symm.trans hc'; cases eq
      have eq := hi.symm.trans hi'; cases eq
      exact ⟨rfl, rfl, rfl⟩

theorem ScalarShape.not_owned (a : ScalarShape g root owner init rest)
    (b : OwnedLendContext.Shape g root owner' init' rest') : False := by
  cases a with
  | intro reader cont refTy resultTy inner ownerTy h _ _ hc result _ _ =>
    cases b with
    | intro reader' cont' _ _ _ resultTy' inner' _ h' _ _ _ _ hc' bounded _ _ =>
      have eq := h.symm.trans h'; cases eq
      have eq := hc.symm.trans hc'; cases eq
      simp [Graph.bufferOne, result] at bounded

def LiteralBound : Result → Prop
  | .literal value => value < 2^63
  | .scalar _ => True

def scalarEvents (s : State) (x : Nat) (reads : List Event) : List Event :=
  .beginLease s.nextLease x :: (reads ++ [.close s.nextLease])

theorem scalar_steps (valid : Valid s) (live : s.live x = true)
    (read : Reads (opened s x) [s.nextLease] r v es) :
    Steps s (scalarEvents s x es) (restored s) := by
  apply Steps.cons (Step.beginLease live)
  apply steps_append (reader_steps read)
  have close : Step (opened s x) (.close s.nextLease) (restored s) := by
    rw [← close_restores (x := x) valid]
    exact Step.close (x := x) (by simp [opened, put])
  exact Steps.cons close Steps.nil

theorem restored_owns (owned : Owns s owners) : Owns (restored s) owners :=
  ⟨owned.distinct, owned.live, owned.leaseFree⟩

end Jihoo.OwnedScalarContext
