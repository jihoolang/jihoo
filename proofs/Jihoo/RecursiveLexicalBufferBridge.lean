import Jihoo.RecursiveLexicalFields
import Jihoo.SizedCoreSafety

/-! Compatibility with the established sized Buffer judgment. The bridge is
restricted to Buffer-only capability inventories; it never reinterprets a
recursive Data capability as a Buffer or invents its dependent length. -/
namespace Jihoo.RecursiveLexicalFields
open HeapLeases LinearHeapPrograms

variable {ctx : List SizedBufferContext.Entry} {env : List SizedBufferContext.Value}
  {owners : List Nat}

def embedEntry : SizedBufferContext.Entry → Entry
  | .nat n => .nat n
  | .scalar => .scalar
  | .owner k => .buffer k
  | .bound _ => .ghost
  | .dead => .dead

def embedValue : SizedBufferContext.Value → Value
  | .nat n => .nat n
  | .scalar n => .scalar n
  | .owner x => .buffer x
  | .borrow x => .borrow x
  | .ghost => .ghost

theorem embedValue_injective {a b : SizedBufferContext.Value}
    (eq : embedValue a = embedValue b) : a = b := by
  cases a <;> cases b <;> simp_all [embedValue]

theorem Agrees.embedded_lookup {k : Nat} (h : Agrees caps (ctx.map embedEntry) (env.map embedValue))
    (found : ctx[k]? = some entry) :
    ∃ value, env[k]? = some value ∧ Rel caps (embedEntry entry) (embedValue value) := by
  obtain ⟨v, lookup, related⟩ := h.lookup (k := k) (e := embedEntry entry) (by simp [List.getElem?_map, found])
  cases original : env[k]? with
  | none => simp [List.getElem?_map, original] at lookup
  | some value =>
    have eq : embedValue value = v := by simpa [List.getElem?_map, original] using lookup
    subst v
    exact ⟨value, rfl, related⟩

theorem buffer_lookup {k : Nat} (h : (owners.map Capability.buffer)[k]? = some (.buffer x)) :
    owners[k]? = some x := by
  cases found : owners[k]? with
  | none => simp [List.getElem?_map, found] at h
  | some y =>
    have eq : y = x := by simpa [List.getElem?_map, found] using h
    simp [eq]

/-- Existing erased-bound metadata remains in the original ctx parameter;
only its runtime ghost slot is embedded. No bound fact is manufactured. -/
theorem Agrees.toSized (h : Agrees (owners.map Capability.buffer)
    (ctx.map embedEntry) (env.map embedValue)) : SizedBufferContext.Agrees ctx owners env := by
  constructor
  · intro k n found
    obtain ⟨v, lookup, related⟩ := h.embedded_lookup found
    have eq : v = .nat n := embedValue_injective related
    simpa [eq] using lookup
  · intro k found
    obtain ⟨v, lookup, n, related⟩ := h.embedded_lookup found
    have eq : v = .scalar n := embedValue_injective related
    exact ⟨n, by simpa [eq] using lookup⟩
  · intro k slot found
    obtain ⟨v, lookup, x, cap, related⟩ := h.embedded_lookup found
    have eq : v = .owner x := embedValue_injective related
    exact ⟨x, buffer_lookup cap, by simpa [eq] using lookup⟩
  · intro k fact found
    obtain ⟨v, lookup, related⟩ := h.embedded_lookup found
    have eq : v = .ghost := embedValue_injective related
    simpa [eq] using lookup

theorem footprint_buffers : footprint (owners.map Capability.buffer) = owners := by
  induction owners with
  | nil => rfl
  | cons x xs ih => simp [footprint, Capability.owners, ih]

/-- The old source judgment still constructs execution and exact resource
accounting from its own typing/layout premises and the new lexical interface.
This is Buffer compatibility, not a source typing rule for data elimination. -/
theorem buffer_total {s : SizedBufferHeap.State} (typed : SizedCoreTyping.Typing g ctx sizes term kind)
    (agreement : Agrees (owners.map Capability.buffer) (ctx.map embedEntry) (env.map embedValue))
    (inventory : Inventory ⟨s.heap, cells⟩ (owners.map Capability.buffer))
    (layout : SizedBufferContext.Layout s owners sizes) (valid : SizedBufferHeap.Valid s) :
    ∃ value events t, SizedCoreExecution.Eval g env term s value events t ∧
      SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧
      SizedCoreTyping.Post kind t value ∧ SizedCoreTyping.Account owners value events := by
  exact typed.total_accounted agreement.toSized layout valid
    (by simpa [footprint_buffers] using inventory.1)

end Jihoo.RecursiveLexicalFields
