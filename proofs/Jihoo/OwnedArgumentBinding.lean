import Jihoo.PureOwnedEnvironment

/-! Single-use ownership transfer into an immediately applied Buffer1 lambda.
The capability list does not change. Older lexical aliases are tombstoned while
the parameter receives the selected identity. This is not unrestricted dependent
substitution or permission to duplicate/capture an owned function value. -/
namespace Jihoo.OwnedArgumentBinding
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext

def invalidate (ctx : Context) (slot : Nat) : Context :=
  ctx.map (fun b => if b = .owner slot then .dead else b)

def transferred (ctx : Context) (slot : Nat) : Context := .owner slot :: invalidate ctx slot

inductive Shape (g : Graph.Graph) (root argument body : Nat) : Prop where
  | intro (function domain : Nat) : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body → Graph.bufferOne g domain = true →
      Shape g root argument body

theorem Shape.head (h : Shape g root arg body) : ∃ f, Graph.nodeAt g root = .app f arg := by
  cases h with | intro f _ head _ _ => exact ⟨f, head⟩

theorem Shape.unique (a : Shape g root arg body) (b : Shape g root arg' body') :
    arg = arg' ∧ body = body' := by
  cases a with
  | intro f ty h hf _ =>
    cases b with
    | intro f' ty' h' hf' _ =>
      have eq := h.symm.trans h'; cases eq
      have eq := hf.symm.trans hf'; cases eq
      exact ⟨rfl, rfl⟩

theorem Shape.not_pure (owned : Shape g root arg body)
    (pure : PureOwnedScalar.Shape g root arg' body') : False := by
  cases owned with
  | intro f ty h hf bound =>
    cases pure with
    | intro f' ty' h' hf' scalar =>
      have eq := h.symm.trans h'; cases eq
      have eq := hf.symm.trans hf'; cases eq
      simp [Graph.bufferOne, scalar] at bound

theorem ownerSlot_variable (resolved : ownerSlot g ctx argument = some slot) :
    ∃ k, Graph.nodeAt g argument = .var k ∧ ctx[k]? = some (.owner slot) := by
  cases shape : Graph.nodeAt g argument <;> simp [ownerSlot, ScalarCoreCallers.ownerSlot, shape] at resolved
  case var k =>
    cases lookup : ctx[k]? with
    | none => simp [lookup] at resolved
    | some b =>
        cases b with
        | scalar | dead => simp [lookup] at resolved
        | owner j =>
            simp [lookup] at resolved
            subst j
            exact ⟨k, rfl, lookup⟩

theorem invalidate_ownerView : ownerView (invalidate ctx slot) =
    (ownerView ctx).map (fun entry => if entry = some slot then none else entry) := by
  simp only [ownerView, ScalarCoreCallers.ownerView, invalidate, List.map_map]
  apply List.map_congr_left
  intro b _
  cases b with
  | owner j => by_cases eq : j = slot <;> simp [eq]
  | scalar | dead => simp

theorem transferred_ownerView : ownerView (transferred ctx slot) =
    some slot :: (ownerView ctx).map (fun entry => if entry = some slot then none else entry) := by
  change some slot :: ownerView (invalidate ctx slot) = _
  rw [invalidate_ownerView]

/-- The parameter gets the selected concrete object; all older selected aliases
are absent, and every unrelated binding keeps its previous concrete identity. -/
theorem transferred_bindings (selected : Select owners slot x rest) :
    LinearCoreCallers.bindings (ownerView (transferred ctx slot)) owners =
      some x :: (ownerView ctx).map (fun entry =>
        if entry = some slot then none else entry.bind (fun k => owners[k]?)) := by
  rw [transferred_ownerView]
  simp only [LinearCoreCallers.bindings, List.map_cons, Option.bind_some,
    LinearCoreCallers.Select.lookup_selected selected, List.map_map]
  congr 1
  apply List.map_congr_left
  intro entry _
  by_cases eq : entry = some slot <;> simp [eq]

theorem scalar_bindings_preserved : scalarBindings (transferred ctx slot) values =
    none :: scalarBindings ctx values := by
  simp only [scalarBindings, ScalarCoreCallers.scalarBindings, transferred, invalidate,
    List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  cases b with
  | owner j => by_cases eq : j = slot <;> simp [eq]
  | scalar | dead => simp

theorem older_alias_dead (lookup : ctx[k]? = some (.owner slot)) :
    (transferred ctx slot)[k + 1]? = some .dead := by
  simp [transferred, invalidate, List.getElem?_map, lookup]

theorem unrelated_binding_preserved (lookup : ctx[k]? = some b) (different : b ≠ .owner slot) :
    (transferred ctx slot)[k + 1]? = some b := by
  simp [transferred, invalidate, List.getElem?_map, lookup, different]

theorem selected_parameter_only :
    (transferred ctx slot)[k]? = some (.owner slot) ↔ k = 0 := by
  cases k with
  | zero => simp [transferred]
  | succ k =>
      simp only [transferred, invalidate, List.getElem?_cons_succ, List.getElem?_map]
      cases lookup : ctx[k]? with
      | none => simp
      | some b => by_cases eq : b = .owner slot <;> simp [eq]

theorem ready_preserved (ready : PureOwnedScalar.Ready ctx values) :
    PureOwnedScalar.Ready (transferred ctx slot) values := by
  intro k scalarSlot lookup
  cases k with
  | zero => simp [transferred] at lookup
  | succ k =>
      simp only [transferred, invalidate, List.getElem?_cons_succ, List.getElem?_map] at lookup
      cases original : ctx[k]? with
      | none => simp [original] at lookup
      | some b =>
          by_cases eq : b = .owner slot
          · simp [original, eq] at lookup
          · simp [original, eq] at lookup
            subst b
            exact ready k scalarSlot original

/-- Adding the owned parameter shifts lexical indices but not scalar captures.
This is a genuine substitution equation for arbitrary existing Raw syntax;
it does not substitute an owned pointer into the pure scalar calculus. -/
theorem closing_shift (raw : CoreBridge.Raw) :
    (raw.rename Nat.succ).subst (PureOwnedScalar.closing (transferred ctx slot) values) =
      raw.subst (PureOwnedScalar.closing ctx values) := by
  rw [CoreBridge.Raw.subst_rename]
  congr 1
  funext k
  simp [PureOwnedScalar.closing, scalar_bindings_preserved]


end Jihoo.OwnedArgumentBinding
