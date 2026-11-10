import Jihoo.OwnedLendTransfer
import Jihoo.LinearCoreCallers

/-! Constructor and lexical identity interface for compositional owned-result
Lend. Only aliases of the selected capability are readable through Borrow;
unrelated owned capabilities remain available to the continuation. -/
namespace Jihoo.OwnedLendContext
open HeapLeases ScopedLend LinearHeapPrograms LinearCoreCallers

inductive Shape (g : Graph.Graph) (root owner init rest : Nat) : Prop where
  | intro (reader cont refTy allocation length resultTy inner ownerTy : Nat) :
      Graph.nodeAt g root = .lend owner reader cont →
      Graph.nodeAt g reader = .lam false refTy allocation →
      Graph.refOne g refTy = true →
      Graph.nodeAt g allocation = .alloc length init →
      Graph.nodeAt g length = .natural 1 →
      Graph.nodeAt g cont = .lam false resultTy inner →
      Graph.bufferOne g resultTy = true →
      Graph.nodeAt g inner = .lam false ownerTy rest →
      Graph.bufferOne g ownerTy = true → Shape g root owner init rest

theorem Shape.unique (a : Shape g root owner init rest)
    (b : Shape g root owner' init' rest') : owner = owner' ∧ init = init' ∧ rest = rest' := by
  cases a with
  | intro reader cont refTy allocation length resultTy inner ownerTy h hr _ ha _ hc _ hi _ =>
    cases b with
    | intro reader' cont' refTy' allocation' length' resultTy' inner' ownerTy' h' hr' _ ha' _ hc' _ hi' _ =>
      have eq := h.symm.trans h'; cases eq
      have eq := hr.symm.trans hr'; cases eq
      have eq := ha.symm.trans ha'; cases eq
      have eq := hc.symm.trans hc'; cases eq
      have eq := hi.symm.trans hi'; cases eq
      exact ⟨rfl, rfl, rfl⟩

theorem Shape.head (h : Shape g root owner init rest) :
    ∃ reader cont, Graph.nodeAt g root = .lend owner reader cont := by
  cases h with
  | intro reader cont _ _ _ _ _ _ head _ _ _ _ _ _ _ _ => exact ⟨reader, cont, head⟩

def readerRoles (ctx : Context) (slot : Nat) : List Graph.Role :=
  .borrow :: ctx.map (fun entry => if entry = some slot then .owner else .ghost)

def returnedContext (ctx : Context) (slot : Nat) : Context := some (slot + 1) :: fresh ctx

/-- The two new lexical names are original-owner then newly allocated result.
All old aliases keep their concrete identities despite compact-slot shifting. -/
theorem returned_bindings (selected : Select owners slot x rest) :
    bindings (returnedContext ctx slot) (freshObject :: owners) =
      some x :: some freshObject :: bindings ctx owners := by
  simp only [returnedContext, bindings, List.map_cons, Option.bind_some,
    List.getElem?_cons_succ, Select.lookup_selected selected]
  exact congrArg (List.cons (some x)) (fresh_bindings (ctx := ctx) (x := freshObject) (owners := owners))

theorem reader_selected_iff :
    (readerRoles ctx slot)[k + 1]? = some .owner ↔ ctx[k]? = some (some slot) := by
  simp only [readerRoles, List.getElem?_cons_succ, List.getElem?_map]
  cases h : ctx[k]? with
  | none => simp
  | some entry => by_cases eq : entry = some slot <;> simp [eq]

theorem reader_borrow_iff :
    (readerRoles ctx slot)[k]? = some .borrow ↔ k = 0 := by
  cases k with
  | zero => simp [readerRoles]
  | succ k =>
      simp only [readerRoles, List.getElem?_cons_succ, List.getElem?_map]
      cases h : ctx[k]? with
      | none => simp
      | some entry => by_cases eq : entry = some slot <;> simp [eq]

theorem unrelated_not_owner (lookup : ctx[k]? = some (some other)) (different : other ≠ slot) :
    (readerRoles ctx slot)[k + 1]? ≠ some .owner := by
  intro role
  have eq := reader_selected_iff.mp role
  simp [lookup, different] at eq

/-- A native-shaped Borrow(original-name) is admitted precisely for an alias
of the selected capability, never merely because the variable is an owner. -/
theorem borrow_original_iff (shape : Graph.nodeAt g root = .borrow varNode)
    (variableShape : Graph.nodeAt g varNode = .var (k + 1)) :
    Graph.borrowOperand g (readerRoles ctx slot) root = true ↔
      ctx[k]? = some (some slot) := by
  simpa [Graph.borrowOperand, shape, variableShape] using
    (reader_selected_iff (ctx := ctx) (slot := slot) (k := k))

theorem borrow_direct_iff (shape : Graph.nodeAt g root = .var k) :
    Graph.borrowOperand g (readerRoles ctx slot) root = true ↔ k = 0 := by
  simpa [Graph.borrowOperand, shape] using
    (reader_borrow_iff (ctx := ctx) (slot := slot) (k := k))

/-- Reading by the original lexical name resolves to the same selected object. -/
theorem reader_owner_identity (role : (readerRoles ctx slot)[k + 1]? = some .owner)
    (selected : Select owners slot x rest) :
    (bindings ctx owners)[k]? = some (some x) := by
  have lookup := reader_selected_iff.mp role
  simp [bindings, List.getElem?_map, lookup, Select.lookup_selected selected]

/-- Consuming the returned original owner also clears every older alias to it,
while the new owned result remains at compact slot zero. -/
theorem consumed_returned_bindings (selected : Select owners slot x rest) :
    bindings (consumed (slot + 1) (returnedContext ctx slot)) (freshObject :: rest) =
      none :: some freshObject :: bindings (consumed slot ctx) rest := by
  rw [consumed_bindings (Select.there selected)]
  simp only [returnedContext, fresh, List.map_cons, Option.some.injEq, ↓reduceIte,
    Option.bind_some, List.getElem?_cons_zero]
  rw [consumed_bindings selected]
  congr 2
  simp only [List.map_map]
  apply List.map_congr_left
  intro entry _
  cases entry with
  | none => simp
  | some k => by_cases eq : k = slot <;> simp [eq]

end Jihoo.OwnedLendContext
