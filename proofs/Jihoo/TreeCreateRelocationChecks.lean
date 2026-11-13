import Jihoo.TreeCreateRelocationCorrectness

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Jihoo.TreeCreateRelocation.Checks
open ReferenceCfg ReferenceCalls TreeCreateCfg
private def q : Slots := ⟨8, 3, 6, 1, 5, 9, 2⟩
private def stop : Block := ⟨#[], .ret⟩
private def types : Array Ty := #[.ptr, .ptr, .ptr, .ptr, .ptr, .ptr, .i64, .i64, .ptr, .ptr]
private def program (node : Bool) (left right : Nat) : Program :=
  #[⟨⟨⟨types, #[stop, build q node 3, stop, stop, entry q node left right 1]⟩,
    #[none, none, none, none, none]⟩, #[]⟩]
private def heap : ReferenceHeap.Heap := #[ReferenceHeap.nilObject, ReferenceHeap.nilObject]
private def saved : List Continuation := [⟨42, 17, #[some (.i64 7)], ⟨2, false⟩⟩]
private def locals : Array (Option Value) :=
  #[none, some (.pointer 1 0), none, some (.pointer 1 0), none,
    some (.pointer 0 0), none, some (.i64 42), some (.pointer 0 0), none]

/-- The swapped-operand fixture satisfies the general theorem's premises,
not merely its independently evaluated conclusion. -/
theorem swapped_placement : Placement ((program true 5 1)[0]'(by decide)) q true 5 1 4 1 3 := by
  constructor <;> decide

theorem swapped_safe : Safe ((program true 5 1)[0]'(by decide)) q locals 5 1 := by
  constructor
  · decide
  · intro k hk
    simp only [Slots.writes, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h | h | h | h | h <;> subst k <;> decide
  · intro k hk
    simp only [Slots.writes, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h | h | h | h | h <;> subst k <;> decide
  all_goals decide

/-- Destinations 1/5 are the reverse of sources 5/1; blocks 4/1/3 and
scratch/result positions are noncontiguous. Suspended caller and local 7 survive. -/
theorem swapped_children :
    walk (program true 5 1) 13 (stateAt 0 4 heap locals saved) =
      some (nodeOut q 0 3 heap 0 1 locals saved, [.alloc 2 24]) := by decide

/-- Both source operands would be destroyed by the original malloc/offset.
They are captured by the real moves before either scratch write occurs. -/
theorem scratch_sources :
    walk (program true 8 3) 13 (stateAt 0 4 heap locals saved) =
      some (nodeOut q 0 3 heap 0 1 locals saved, [.alloc 2 24]) := by decide

theorem relocated_nil :
    walk (program false 5 1) 3 (stateAt 0 4 heap locals saved) =
      some (nilOut q 0 3 heap locals saved, [.alloc 2 8]) := by decide

theorem equal_sources :
    walk (program true 5 5) 13 (stateAt 0 4 heap locals saved) =
      some (nodeOut q 0 3 heap 0 0 locals saved, [.alloc 2 24]) := by decide

/-- Raw construction never dereferences child values. These examples are NOT
ownership/layout witnesses and therefore do not invoke node_total. -/
theorem dangling_children :
    walk (program true 5 1) 13
      (stateAt 0 4 #[] ((locals.set! 5 (some (.pointer 99 0))).set! 1 (some (.pointer 100 0))) []) =
    some (nodeOut q 0 3 #[] 99 100
      ((locals.set! 5 (some (.pointer 99 0))).set! 1 (some (.pointer 100 0))) [], [.alloc 0 24]) := by decide

theorem null_child :
    (walk (program true 5 1) 13
      (stateAt 0 4 #[] ((locals.set! 5 (some .null)).set! 1 (some (.pointer 99 7))) [])).map
      (fun out => out.1.frame.heap) =
    some #[ReferenceHeap.node .null (.object 99 7)] := by decide

theorem missing_child_rejected :
    walk (program true 0 1) 13 (stateAt 0 4 heap locals saved) = none := by decide

/-- Four copies run before malloc checks the actual object/cell budgets. -/
theorem object_budget_rejected :
    walk (program true 5 1) 5
      (stateAt 0 4 (Array.replicate 512 ReferenceHeap.nilObject) locals saved) = none := by decide

theorem cell_budget_rejected :
    walk (program true 5 1) 5
      (stateAt 0 4 #[⟨true, Array.replicate 4094 none⟩] locals saved) = none := by decide

private def callProgram : Program :=
  #[⟨⟨⟨types.set! 7 .unit, #[stop, build q true 3, stop, stop, entry q true 5 1 1]⟩,
    #[none, none, none, none, none]⟩, #[]⟩]

/-- parameters=[] does not bind children. Ordinary enter with two arguments
fails instead of manufacturing the initial operand hypotheses. -/
theorem call_does_not_bind_children :
    enter callProgram (stateAt 0 4 heap (locals.set! 7 (some .unit)) [])
      ⟨0, #[arg 5, arg 1], ⟨7, false⟩, 3⟩ = none := by decide

end Jihoo.TreeCreateRelocation.Checks
