import Jihoo.ScopedLend

namespace Jihoo.ScopedLend.Examples
open HeapLeases

/-- Object 0 has an ambient lease; object 1 is exclusively owned by this Lend. -/
def initial : State :=
  ⟨2, 1, fun x => x < 2, fun x => if x = 0 then 41 else 42,
    fun l => if l = 0 then some 0 else none⟩

theorem initial_valid : Valid initial := by
  constructor
  · intro x live; simpa [initial] using live
  · intro l x lookup
    simp only [initial] at lookup
    split at lookup
    · next h => simp only [Option.some.injEq] at lookup; subst l; subst x; decide
    · contradiction

theorem owner_available : Unborrowed initial 1 := by
  intro l
  simp only [initial]
  split <;> decide

def body : Reader := .seq (.read 0) (.branch false (.scalar 7) (.read 0))

theorem body_scoped : Scoped 1 body := .seq (.read (by decide))
  (.branch .scalar (.read (by decide)))

theorem body_reads : Reads (opened initial 1) [initial.nextLease] body 42
    [.read 1 42, .read 1 42] := by
  exact .seq (.read (k := 0) (x := 1) rfl rfl) (.no (.read (k := 0) (x := 1) rfl rfl))

theorem execution : Executes initial 1 body .storeResult 42
    [.beginLease 1 1, .read 1 42, .read 1 42, .close 1, .write 1 42, .free 1]
    (finalState initial 1 42 .storeResult) := .lend body_reads

theorem execution_safe :
    Valid (finalState initial 1 42 .storeResult) ∧
    (released [.beginLease 1 1, .read 1 42, .read 1 42, .close 1, .write 1 42, .free 1]).count 1 = 1 ∧
    (finalState initial 1 42 .storeResult).live 1 = false :=
  lend_owner_dead initial_valid (by decide) owner_available execution

theorem totality_example : ∃ v es t, Executes initial 1 body .free v es t ∧ Steps initial es t :=
  lend_total initial_valid (by decide) owner_available body_scoped

theorem ambient_lease_retained : (finalState initial 1 42 .storeResult).lease 0 = some 0 := rfl

theorem ambient_owner_live : (finalState initial 1 42 .storeResult).live 0 = true := by decide

theorem reader_token_gone : (finalState initial 1 42 .storeResult).lease 1 = none := rfl

theorem expired_unreadable :
    ¬ Step (finalState initial 1 42 .storeResult) (.read 1 v) t :=
  execution_token_expires initial_valid execution .nil

theorem reader_cannot_close : ReaderEvents 1 [.read 1 42, .read 1 42] :=
  reader_authority body_reads

theorem wrong_slot_rejected : ¬ Scoped 1 (.read 1) := by
  intro h; cases h; omega

/-- Dead branches are still statically checked, not used to launder bad slots. -/
theorem unselected_bad_slot_rejected : ¬ Scoped 1 (.branch true (.scalar 3) (.read 1)) := by
  intro h; cases h with
  | branch _ bad => exact wrong_slot_rejected bad

theorem wrong_read_value_rejected : ¬ Reads (opened initial 1) [initial.nextLease] (.read 0) 7 es := by
  intro h
  obtain ⟨l, x, slot, lease, value⟩ := read_observation h
  simp [initial] at slot
  subst l
  simp [opened, initial, put] at lease
  subst x
  contradiction

/-- A preexisting borrow of the target owner invalidates lease-free entry. -/
theorem borrowed_entry_rejected : ¬ Unborrowed initial 0 := by
  intro h; exact h 0 rfl

theorem original_name_execution : Executes initial 1 body .freeOriginal 42
    [.beginLease 1 1, .read 1 42, .read 1 42, .close 1, .free 1]
    (finalState initial 1 42 .freeOriginal) := .lend body_reads

theorem returned_and_original_agree :
    finalState initial 1 42 .free = finalState initial 1 42 .freeOriginal := rfl

theorem double_alias_rejected :
    Quantity.LendProjection.checkedLend 0 .unrestricted .pure (.seq (.use 0) (.use 2)) = none := by
  decide

theorem omitted_owner_rejected :
    Quantity.LendProjection.checkedLend 0 .unrestricted .pure .pure = none := by decide

end Jihoo.ScopedLend.Examples
