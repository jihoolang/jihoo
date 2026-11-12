import Jihoo.SymbolicCommonDataSource
import Jihoo.SymbolicCoreCompaction
import Jihoo.CommonDataErasure

/-! Structural support for the two independent lexical masks. Common runtime
retains Data; Core projection removes it. Retired aliases keep their old slots.
No execution or lowering certificate occurs in these support laws. -/
namespace Jihoo.CommonDataCoreSupports
open SymbolicCommonDataContext

def EntrySupports : Entry → Option Bool → Option Bool → Prop
  | .nat, common, core | .scalar, common, core | .buffer _, common, core =>
      common = some true ∧ core = some true
  | .data _, common, _ => common = some true
  | .ghost, _, _ | .dead, _, _ => True

def Supports (ctx : Context) (slots coreMask : List Bool) : Prop :=
  ∀ (k : Nat) (e : Entry), ctx[k]? = some e → EntrySupports e slots[k]? coreMask[k]?

theorem Supports.cons (h : Supports ctx slots coreMask)
    (head : EntrySupports e (some common) (some core)) :
    Supports (e :: ctx) (common :: slots) (core :: coreMask) := by
  intro k entry lookup
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
    subst entry
    exact head
  | succ k => exact h k entry lookup

theorem Supports.map (h : Supports ctx slots coreMask)
    (weaken : ∀ e s c, EntrySupports e s c → EntrySupports (f e) s c) :
    Supports (ctx.map f) slots coreMask := by
  intro k e lookup
  simp only [List.getElem?_map] at lookup
  obtain ⟨old, found, rfl⟩ := Option.map_eq_some_iff.mp lookup
  exact weaken old _ _ (h k old found)

theorem Supports.project (h : Supports ctx slots coreMask) :
    SymbolicCoreCompaction.MaskSupports (SymbolicCommonDataContext.project count ctx) coreMask := by
  intro k e lookup
  simp only [SymbolicCommonDataContext.project, List.getElem?_map] at lookup
  obtain ⟨old, found, rfl⟩ := Option.map_eq_some_iff.mp lookup
  have supported := h k old found
  cases old <;> try { simp_all [projectEntry, EntrySupports, SymbolicCoreCompaction.EntrySupports] }
  rename_i slot
  by_cases bound : slot < count
  · simp only [projectEntry, bound, ↓reduceIte, SymbolicCoreCompaction.EntrySupports]
  · simpa only [projectEntry, bound, ↓reduceIte, SymbolicCoreCompaction.EntrySupports] using supported.2

theorem Supports.data_kept {k slot : Nat} (h : Supports ctx slots coreMask)
    (lookup : ctx[k]? = some (.data slot)) : slots[k]? = some true := h k _ lookup

theorem Supports.buffer_kept {k slot : Nat} (h : Supports ctx slots coreMask)
    (lookup : ctx[k]? = some (.buffer slot)) : slots[k]? = some true := (h k _ lookup).1

theorem position_of_kept (kept : slots[k]? = some true) :
    CommonDataErasure.position slots k = some (SizedErasure.rank slots k) := by
  induction slots generalizing k with
  | nil => simp at kept
  | cons b rest ih =>
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at kept; subst b; rfl
    | succ k => cases b <;> simp [CommonDataErasure.position, SizedErasure.rank, ih kept]

theorem Supports.freshBuffer (h : Supports ctx slots coreMask) :
    Supports (freshBuffer count ctx) (true :: slots) (true :: coreMask) := by
  apply Supports.cons (e := .buffer count) (h.map ?_) (by trivial)
  intro e s c he
  cases e <;> exact he

theorem Supports.consumeBuffer (h : Supports ctx slots coreMask) :
    Supports (consumeBuffer slot ctx) slots coreMask := by
  apply h.map
  intro e s c he
  cases e <;> try exact he
  rename_i k
  by_cases eq : k = slot <;> simp only [consumeBufferEntry, eq, ↓reduceIte] <;> first | exact he | trivial

theorem Supports.bufferCall (h : Supports ctx slots coreMask) :
    Supports (bufferCall count p ctx) (true :: slots) (true :: coreMask) := by
  apply Supports.cons (e := .buffer count) (h.map ?_) (by trivial)
  intro e s c he
  cases e <;> try exact he
  rename_i k
  by_cases bound : count+p ≤ k <;> simp only [bufferCallEntry, bound, ↓reduceIte] <;> first | exact he | trivial

theorem Supports.removeHead (h : Supports ctx slots coreMask) :
    Supports (removeHead ctx) slots coreMask := by
  apply h.map
  intro e s c he
  cases e <;> try exact he
  all_goals rename_i k; cases k <;> simp_all [removeEntry, EntrySupports]

theorem Supports.dataContinuation (h : Supports ctx slots coreMask) :
    Supports (dataContinuation ctx) (true :: slots) (false :: coreMask) := by
  apply Supports.cons (e := .data 0) (h.map ?_) rfl
  intro e s c he
  cases e <;> simp_all [retireAll, EntrySupports]

theorem Supports.argumentContext (h : Supports ctx slots coreMask) :
    Supports (argumentContext a r b ctx) slots coreMask := by
  apply h.map
  intro e s c he
  cases e <;> try exact he
  · rename_i k
    by_cases bound : a+r ≤ k ∧ k < a+r+b <;> simp only [argumentEntry, bound, ↓reduceIte] <;> first | exact he | trivial
  · rename_i k
    by_cases bound : k < a <;> simp only [argumentEntry, bound, ↓reduceIte] <;> first | exact he | trivial

theorem Supports.capturedContext (h : Supports ctx slots coreMask) :
    Supports (capturedContext a r b ctx) (true :: slots) (false :: coreMask) := by
  apply Supports.cons (e := .data 0) (h.map ?_) rfl
  intro e s c he
  cases e <;> try exact he
  · rename_i k
    by_cases bound : a+r+b ≤ k <;> simp only [capturedEntry, bound, ↓reduceIte] <;> first | exact he | trivial
  · rename_i k
    by_cases bound : a ≤ k ∧ k < a+r <;> simp only [capturedEntry, bound, ↓reduceIte] <;> first | exact he | trivial

theorem Supports.continuation (h : Supports ctx slots coreMask) :
    Supports (continuation count ctx) (true :: slots) (true :: coreMask) := by
  apply Supports.cons (e := .scalar) (h.map ?_) (by trivial)
  intro e s c he
  cases e <;> try exact he
  · trivial
  · rename_i k
    by_cases bound : k < count <;> simp only [retainedEntry, bound, ↓reduceIte] <;> first | exact he | trivial

theorem Supports.bindContext (h : Supports ctx slots coreMask) :
    Supports (bindContext ctx) (true :: true :: slots) (false :: false :: coreMask) := by
  apply Supports.cons (e := .data 1) (Supports.cons (e := .data 0) (h.map ?_) rfl) rfl
  intro e s c he
  cases e <;> try exact he
  all_goals rename_i k; cases k <;> simp_all [retireEntry, EntrySupports]

end Jihoo.CommonDataCoreSupports
