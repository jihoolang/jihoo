import Jihoo.RecursiveLexicalBufferBridge

/-! A lexical projection for Buffer bodies under retained recursive capabilities.
Indices are unchanged. Data is hidden, never reinterpreted as Buffer; erased
slots do not manufacture bound evidence. -/
namespace Jihoo.RecursiveBodyProjection
open RecursiveLexicalFields

/-- Only Buffer capabilities beyond the retained prefix are accessible. -/
def entry (skip : Nat) : Entry → SizedBufferContext.Entry
  | .nat n => .nat n
  | .scalar => .scalar
  | .buffer k => if k < skip then .dead else .owner (k - skip)
  | .data _ | .ghost | .dead => .dead

def value : Value → SizedBufferContext.Value
  | .nat n => .nat n
  | .scalar n => .scalar n
  | .buffer x => .owner x
  | .borrow x => .borrow x
  | .data _ | .ghost => .ghost

def context (skip : Nat) (ctx : List Entry) := ctx.map (entry skip)
def environment (env : List Value) := env.map value

/-- The body consumes its Buffer suffix; only the retained Data prefix remains
usable in the old environment. A returned scalar gets a fresh lexical slot. -/
def retainedEntry (count : Nat) : Entry → Entry
  | .buffer _ => .dead
  | .data k => if k < count then .data k else .dead
  | other => other

def continuation (count : Nat) (ctx : List Entry) :=
  Entry.scalar :: ctx.map (retainedEntry count)

variable {owners : List Nat} {retained : List Capability}

theorem project_rel (h : Rel (retained ++ owners.map Capability.buffer) e v) :
    Rel (owners.map Capability.buffer) (embedEntry (entry retained.length e))
      (embedValue (value v)) := by
  cases e with
  | nat n => have eq : v = .nat n := h; subst v; rfl
  | scalar => obtain ⟨n, rfl⟩ := h; exact ⟨n, rfl⟩
  | buffer k =>
    by_cases bound : k < retained.length
    · simp [entry, bound, embedEntry, Rel]
    · obtain ⟨x, lookup, rfl⟩ := h
      have tail : (owners.map Capability.buffer)[k-retained.length]? = some (.buffer x) := by
        simpa [List.getElem?_append, bound] using lookup
      simp only [entry, bound, ite_false, embedEntry, value, embedValue]
      exact ⟨x, tail, rfl⟩
  | data _ | ghost | dead => trivial

theorem project_agrees (h : Agrees (retained ++ owners.map Capability.buffer) ctx env) :
    SizedBufferContext.Agrees (context retained.length ctx) owners (environment env) := by
  apply Agrees.toSized
  induction h with
  | nil => exact .nil
  | cons first _ ih => exact .cons (project_rel first) ih

theorem retain_rel (h : Rel (retained ++ suffix) e v) :
    Rel retained (retainedEntry retained.length e) v := by
  cases e with
  | buffer _ => trivial
  | data k =>
    by_cases bound : k < retained.length
    · obtain ⟨tree, lookup, eq⟩ := h
      have first : retained[k]? = some (.data tree) := by
        simpa [List.getElem?_append, bound] using lookup
      simp only [retainedEntry, bound, ite_true]
      exact ⟨tree, first, eq⟩
    · simp [retainedEntry, bound, Rel]
  | nat _ | scalar | ghost | dead => exact h

theorem retain_agrees (h : Agrees (retained ++ suffix) ctx env) :
    Agrees retained (ctx.map (retainedEntry retained.length)) env := by
  induction h with
  | nil => exact .nil
  | cons first _ ih => exact .cons (retain_rel first) ih

theorem continuation_agrees (h : Agrees (retained ++ suffix) ctx env) :
    Agrees retained (continuation retained.length ctx) (.scalar result :: env) :=
  .cons ⟨result, rfl⟩ (retain_agrees h)

end Jihoo.RecursiveBodyProjection
