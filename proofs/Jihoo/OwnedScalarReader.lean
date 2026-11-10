import Jihoo.OwnedScalarContext

/-! Explicit nonnegative-I64 range boundary. Heap payloads are Nat in this
model; range preservation requires bounded live payloads and bounded reader
literals, rather than silently treating every Nat as a machine I64. -/
namespace Jihoo.OwnedScalarReader
open HeapLeases ScopedLend

def Bounded : Reader → Prop
  | .scalar v => v < 2^63
  | .read _ => True
  | .seq a b | .branch _ a b => Bounded a ∧ Bounded b

def PayloadsBounded (s : State) : Prop := ∀ x, s.live x = true → s.payload x < 2^63

theorem graph_integer_bound (valid : Graph.valid g = true)
    (shape : Graph.nodeAt g root = .integer value) : value < 2^63 := by
  have inside : root < g.size := by
    by_cases h : root < g.size
    · exact h
    have absent : g[root]? = none := Array.getElem?_eq_none (by omega)
    simp [Graph.nodeAt, absent] at shape
  have nodes : (List.range g.size).all (fun id =>
    (Graph.nodeAt g id).children.all (· < id) && match Graph.nodeAt g id with
      | .integer v => v < 2^63
      | .natural v => v < 2^64
      | .var k => k < 2^32
      | _ => true) = true := (Bool.and_eq_true_iff.mp valid).2
  have atRoot := List.all_eq_true.mp nodes root (List.mem_range.mpr inside)
  simpa [shape] using (Bool.and_eq_true_iff.mp atRoot).2

theorem represented_bounded (valid : Graph.valid g = true)
    (h : Graph.Represents g ctx root r) : Bounded r := by
  induction h with
  | scalar shape => exact graph_integer_bound valid shape
  | read => trivial
  | strict _ _ _ ia ib | app _ _ _ _ _ ia ib | branch _ _ _ _ _ _ _ ia ib => exact ⟨ia, ib⟩

theorem reads_bounded (valid : Valid s) (payloads : PayloadsBounded s)
    (bounded : Bounded r) (read : Reads s env r v es) : v < 2^63 := by
  induction read with
  | scalar => exact bounded
  | read _ lease => exact payloads _ (valid.leased _ _ lease).2
  | seq _ _ _ ib => exact ib bounded.2
  | yes _ ih => exact ih bounded.1
  | no _ ih => exact ih bounded.2

theorem opened_payloads (payloads : PayloadsBounded s) : PayloadsBounded (opened s x) := payloads

theorem restored_payloads (payloads : PayloadsBounded s) : PayloadsBounded (restored s) := payloads

theorem allocated_payloads (payloads : PayloadsBounded s) (bounded : v < 2^63) :
    PayloadsBounded (LinearHeapPrograms.allocatedState s v) := by
  intro x live
  by_cases fresh : x = s.nextObject
  · subst x; simpa [LinearHeapPrograms.allocatedState, put] using bounded
  · simp [LinearHeapPrograms.allocatedState, put, fresh] at live ⊢
    exact payloads x live

end Jihoo.OwnedScalarReader
