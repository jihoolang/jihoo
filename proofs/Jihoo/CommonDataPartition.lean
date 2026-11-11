import Jihoo.CommonDataSyntax

/-! Static prefix partitions split logical capability slots, including empty
Data capabilities. Runtime lexical positions are never removed. -/
namespace Jihoo.CommonData
open RecursiveFieldRuntime RecursiveFieldOwnership RecursiveLexicalFields

/-- Argument receives the selected Data and Buffer prefixes, densely numbered. -/
def argumentEntry (dataCount retainedCount bufferCount : Nat) : Entry → Entry
  | .data k => if k < dataCount then .data k else .dead
  | .buffer k => if dataCount + retainedCount ≤ k ∧ k < dataCount + retainedCount + bufferCount
      then .buffer (k - retainedCount) else .dead
  | e => e

def argumentContext (dataCount retainedCount bufferCount : Nat) (ctx : List Entry) :=
  ctx.map (argumentEntry dataCount retainedCount bufferCount)

/-- All aliases of consumed capabilities are retired. Retained capabilities
follow the actual returned Data tree in the continuation inventory. -/
def capturedEntry (dataCount retainedCount bufferCount : Nat) : Entry → Entry
  | .data k => if dataCount ≤ k ∧ k < dataCount + retainedCount
      then .data (1 + (k - dataCount)) else .dead
  | .buffer k => if dataCount + retainedCount + bufferCount ≤ k
      then .buffer (1 + retainedCount + (k - (dataCount + retainedCount + bufferCount))) else .dead
  | e => e

def capturedContext (dataCount retainedCount bufferCount : Nat) (ctx : List Entry) :=
  Entry.data 0 :: ctx.map (capturedEntry dataCount retainedCount bufferCount)

/-- A Data slot cannot be authorized on both sides, even for empty trees. -/
theorem data_partition_disjoint :
    argumentEntry a r b (.data k) = .dead ∨ capturedEntry a r b (.data k) = .dead := by
  by_cases h : k < a
  · right; simp [capturedEntry, show ¬ a ≤ k by omega]
  · left; simp [argumentEntry,h]

/-- Buffer authority is also split by slot, not by coincident runtime IDs. -/
theorem buffer_partition_disjoint :
    argumentEntry a r b (.buffer k) = .dead ∨ capturedEntry a r b (.buffer k) = .dead := by
  by_cases h : a + r ≤ k ∧ k < a + r + b
  · right; simp [capturedEntry, show ¬ a+r+b ≤ k by omega]
  · left; simp [argumentEntry,h]

variable {active retained : List Tree} {used saved : List Nat}

theorem rel_argument (h : Rel (caps (active ++ retained) (used ++ saved)) e v) :
    Rel (caps active used) (argumentEntry active.length retained.length used.length e) v := by
  cases e with
  | data k =>
    by_cases bound : k < active.length
    · obtain ⟨tree,lookup,eq⟩ := h
      simp only [argumentEntry, bound]
      refine ⟨tree, ?_, eq⟩
      simpa [caps, List.map_append, List.getElem?_append, bound] using lookup
    · simp [argumentEntry, bound, Rel]
  | buffer k =>
    by_cases bound : active.length + retained.length ≤ k ∧ k < active.length + retained.length + used.length
    · obtain ⟨x,lookup,eq⟩ := h
      simp only [argumentEntry, bound]
      refine ⟨x, ?_, eq⟩
      have a : ¬ k < active.length := by omega
      have r : ¬ k - active.length < retained.length := by omega
      have b : k - active.length - retained.length < used.length := by omega
      have n : ¬ k - retained.length < active.length := by omega
      have same : k - retained.length - active.length = k - active.length - retained.length := by omega
      simpa [caps, List.map_append, List.append_assoc, List.getElem?_append, a, r, b, n, same] using lookup
    · simp [argumentEntry, bound, Rel]
  | nat _ | scalar | ghost | dead => exact h

theorem rel_captured (h : Rel (caps (active ++ retained) (used ++ saved)) e v) :
    Rel (caps (result :: retained) saved)
      (capturedEntry active.length retained.length used.length e) v := by
  cases e with
  | data k =>
    by_cases bound : active.length ≤ k ∧ k < active.length + retained.length
    · obtain ⟨tree,lookup,eq⟩ := h
      simp only [capturedEntry, bound]
      refine ⟨tree, ?_, eq⟩
      have a : ¬ k < active.length := by omega
      have r : k - active.length < retained.length := by omega
      simpa [caps, List.map_append, List.append_assoc, List.getElem?_append, a, r, Nat.add_comm] using lookup
    · simp [capturedEntry, bound, Rel]
  | buffer k =>
    by_cases bound : active.length + retained.length + used.length ≤ k
    · obtain ⟨x,lookup,eq⟩ := h
      simp only [capturedEntry, bound]
      refine ⟨x, ?_, eq⟩
      have a : ¬ k < active.length := by omega
      have r : ¬ k - active.length < retained.length := by omega
      have b : ¬ k - active.length - retained.length < used.length := by omega
      have n : ¬ retained.length + (k - (active.length + retained.length + used.length)) < retained.length := by omega
      have same : k - active.length - retained.length - used.length = k - (active.length + retained.length + used.length) := by omega
      have index : 1 + retained.length + (k - (active.length + retained.length + used.length)) = (retained.length + (k - (active.length + retained.length + used.length))) + 1 := by omega
      rw [index]
      simp only [caps, List.map_cons, List.cons_append, List.getElem?_cons_succ]
      simpa [caps, List.map_append, List.append_assoc, List.getElem?_append, a, r, b, n, same] using lookup
    · simp [capturedEntry, bound, Rel]
  | nat _ | scalar | ghost | dead => exact h

theorem agrees_argument (h : Agrees (caps (active ++ retained) (used ++ saved)) ctx env) :
    Agrees (caps active used) (argumentContext active.length retained.length used.length ctx) env := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (rel_argument head) ih

theorem agrees_captured (h : Agrees (caps (active ++ retained) (used ++ saved)) ctx env) :
    Agrees (caps (result :: retained) saved)
      (capturedContext active.length retained.length used.length ctx) (.data (root result) :: env) := by
  change Agrees _ (.data 0 :: _) _
  refine Agrees.cons ⟨result,rfl,rfl⟩ ?_
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (rel_captured head) ih

end Jihoo.CommonData
