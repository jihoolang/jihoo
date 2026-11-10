import Jihoo.HeapLeases

namespace Jihoo.HeapLeases.Examples

def allocated : State :=
  { empty with nextObject := 1, live := put empty.live 0 true,
               payload := put empty.payload 0 42 }
def borrowed : State :=
  { allocated with nextLease := 1, lease := put allocated.lease 0 (some 0) }
def nested : State :=
  { borrowed with nextLease := 2, lease := put borrowed.lease 1 (some 0) }
def innerClosed : State := { nested with lease := put nested.lease 1 none }
def closed : State := { innerClosed with lease := put innerClosed.lease 0 none }
def freed : State := { closed with live := put closed.live 0 false }

theorem allocation : Step empty (.alloc 0 42) allocated := .alloc

theorem opening : Step allocated (.beginLease 0 0) borrowed :=
  .beginLease (by decide)

theorem nested_reader : Steps borrowed [.beginLease 1 0, .read 1 42, .close 1, .read 0 42]
    innerClosed := by
  apply Steps.cons (Step.beginLease (by decide))
  apply Steps.cons (Step.read (x := 0) (by decide))
  apply Steps.cons (Step.close (x := 0) (by decide))
  exact Steps.cons (Step.read (x := 0) (by decide)) .nil

theorem full_lifetime : Steps empty
    [.alloc 0 42, .beginLease 0 0, .beginLease 1 0, .read 1 42,
     .close 1, .read 0 42, .close 0, .free 0] freed := by
  apply Steps.cons allocation
  apply Steps.cons opening
  apply Steps.cons (Step.beginLease (by decide))
  apply Steps.cons (Step.read (x := 0) (by decide))
  apply Steps.cons (Step.close (x := 0) (by decide))
  apply Steps.cons (Step.read (x := 0) (by decide))
  apply Steps.cons (Step.close (x := 0) (by decide))
  apply Steps.cons (Step.free (by decide) ?_)
  · exact .nil
  · intro l
    simp only [borrowed, allocated, empty, put]
    split <;> simp_all

theorem nested_keeps_value : innerClosed.payload 0 = borrowed.payload 0 :=
  (reader_steps (l := 0) (step_valid (step_valid empty_valid allocation) opening)
    (by decide) (by simp [ReaderEvents]) nested_reader).2.2

theorem live_lease_blocks_free : ¬ Step borrowed (.free 0) t :=
  borrowed_not_freed (l := 0) (by decide)

theorem live_lease_blocks_write : ¬ Step borrowed (.write 0 7) t :=
  borrowed_not_written (l := 0) (by decide)

theorem inner_closed_outer_still_blocks_free : ¬ Step innerClosed (.free 0) t :=
  borrowed_not_freed (l := 0) (by decide)

theorem wrong_payload_rejected : ¬ Step borrowed (.read 0 7) t := by
  intro h
  obtain ⟨x, hx, _, hv⟩ := read_live
    (step_valid (step_valid empty_valid allocation) opening) h
  simp [borrowed, allocated, empty, put] at hx
  subst x
  contradiction

theorem freed_not_live : freed.live 0 = false := by decide

theorem completed_valid : Valid freed := steps_valid empty_valid full_lifetime

/-- Reallocating after a free produces object 1, never resurrecting object 0. -/
theorem allocation_does_not_resurrect :
    (put freed.live freed.nextObject true) 0 = false := by decide

/-- A lease token from a closed region cannot read a later allocation. -/
theorem old_token_after_allocation :
    ¬ Step { freed with nextObject := 2, live := put freed.live 1 true,
                        payload := put freed.payload 1 99 } (.read 0 v) t := by
  intro h
  cases h with
  | read present => simp [freed, closed, innerClosed, nested, borrowed, allocated, empty, put] at present

/-- Without the reader authority restriction, a reader could close the token
and write the owner. This execution is deliberately NOT a permitted region. -/
def earlyClosed : State := { borrowed with lease := put borrowed.lease 0 none }
def changed : State := { earlyClosed with payload := put earlyClosed.payload 0 7 }

theorem close_authority_necessary :
    Steps borrowed [.close 0, .write 0 7] changed ∧
    ¬ ReaderEvents 0 [.close 0, .write 0 7] ∧ changed.payload 0 ≠ borrowed.payload 0 := by
  refine ⟨?_, by simp [ReaderEvents], by decide⟩
  apply Steps.cons (Step.close (x := 0) (by decide))
  apply Steps.cons (Step.write (by decide) ?_)
  · exact .nil
  · intro l
    simp only [borrowed, allocated, empty, put]
    split <;> simp_all

/-- Quantity and heap traces agree on identity 0 in this concrete complete run. -/
theorem quantity_heap_endpoint :
    (released [.alloc 0 42, .beginLease 0 0, .beginLease 1 0, .read 1 42,
      .close 1, .read 0 42, .close 0, .free 0]).count 0 = 1 ∧ freed.live 0 = false := by
  apply checked_owner_released empty_valid full_lifetime
    (c := Quantity.Control.use 0)
  · exact Quantity.Finishes.use
  · rfl

end Jihoo.HeapLeases.Examples
