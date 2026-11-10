import Jihoo.InitializationCalls

namespace Jihoo.Initialization.Calls.Examples

def caller : Function := ⟨2, false,
  [(0, .call 1 [.slot 1, .constant 0] 1 1),
   (1, .action ⟨[1, 2], [0]⟩ 2), (2, .ret)],
  fun pc => ([some [1, 2], some [1, 2], some [0]])[pc]?.join⟩

def recursive : Function := ⟨2, false,
  [(0, .branch [1] [1, 2]), (1, .call 1 [.slot 1, .slot 2] 0 2),
   (2, .action ⟨[1, 2], [0]⟩ 3), (3, .ret)],
  fun pc => ([some [1, 2], some [1, 2], some [1, 2], some [0]])[pc]?.join⟩

def program : Program := [caller, recursive]

theorem recursive_program_accepted : validate program = true := by decide

theorem recursive_execution_safe
    (reach : Reaches program unit constants
      (.active 0 0 (caller.entry unit [a, b]) []) state) : state ≠ .uninitialized :=
  no_uninitialized (validate_sound recursive_program_accepted) (by rfl) (by rfl) reach

def saved : Resume Nat := ⟨0, 1, 1, caller.entry 0 [11, 22]⟩

theorem call_pushes_caller :
    Step program 0 (fun n => n + 100)
      (.active 0 0 (caller.entry 0 [11, 22]) [])
      (.active 1 0 (recursive.entry 0 [11, 100]) [saved]) :=
  .call (args := [.slot 1, .constant 0]) rfl (by simp [caller]) rfl rfl rfl

theorem return_restores_caller :
    Step program 0 (fun n => n + 100)
      (.active 1 3 (Store.enter (some 7) [99, 888]) [saved])
      (.active 0 1 (Store.write saved.memory 1 7) []) :=
  .ret rfl (by simp [recursive]) rfl

theorem argument_order :
    readArguments (fun n => n + 100) (Store.enter none [11, 22])
      [.slot 2, .constant 3, .slot 1, .slot 2] = some [22, 103, 11, 22] := rfl

theorem argument_missing :
    readArguments (fun n => n) (Store.enter none [11]) [.slot 2] = none := rfl

theorem caller_cell_survives_return :
    Store.write (Store.enter none [11, 22]) 1 (7 : Nat) 2 = some 22 := rfl

theorem returned_value_installed :
    Store.write (Store.enter none [11, 22]) 1 (7 : Nat) 1 = some 7 := rfl

theorem invalid_callee_rejected :
    validate [{ caller with code := [(0, .call 9 [.slot 1, .slot 2] 1 1),
      (1, .action ⟨[1, 2], [0]⟩ 2), (2, .ret)] }, recursive] = false := by decide

theorem invalid_arity_rejected :
    validate [{ caller with code := [(0, .call 1 [.slot 1] 1 1),
      (1, .action ⟨[1, 2], [0]⟩ 2), (2, .ret)] }, recursive] = false := by decide

theorem unsaved_caller_local_rejected :
    validate [{ caller with code := [(0, .call 1 [.slot 1, .slot 2] 1 1),
      (1, .action ⟨[1, 3], [0]⟩ 2), (2, .ret)] }, recursive] = false := by decide

theorem missing_return_value_rejected :
    validate [⟨0, false, [(0, .ret)], fun _ => some []⟩] = false := by decide

theorem unit_return_accepted :
    validate [⟨0, true, [(0, .ret)], fun _ => some [0]⟩] = true := by decide

end Jihoo.Initialization.Calls.Examples
