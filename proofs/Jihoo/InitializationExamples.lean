import Jihoo.Initialization

namespace Jihoo.Initialization.Examples

def loop : Graph := [
  (0, ⟨[⟨[], [1]⟩], [1]⟩),
  (1, ⟨[⟨[1], []⟩], [1]⟩)]
def loopCert : Certificate
  | 0 => some []
  | 1 => some [1]
  | _ => none

theorem cycle_accepted : check loop [] loopCert = true := by decide

theorem loop_reads (reach : Reach loop [] pc state) (member : (pc, b) ∈ loop) :
    Safe b.actions state := accepted_reads_safe cycle_accepted reach member

theorem read_before_write_rejected :
    check [(0, ⟨[⟨[1], [1]⟩], []⟩)] [] (fun _ => some []) = false := by decide

def join : Graph := [
  (0, ⟨[], [1, 2]⟩), (1, ⟨[⟨[], [3]⟩], [3]⟩),
  (2, ⟨[], [3]⟩), (3, ⟨[⟨[3], []⟩], []⟩)]
def joinCert : Certificate
  | 3 => some [3]
  | _ => some []

theorem missing_predecessor_rejected : check join [] joinCert = false := by decide

theorem invented_entry_rejected :
    check [(0, ⟨[], []⟩)] [] (fun _ => some [9]) = false := by decide

theorem hidden_successor_rejected :
    check [(0, ⟨[], [1]⟩), (1, ⟨[], []⟩)] []
      (fun | 0 => some [] | _ => none) = false := by decide

theorem unreachable_accepted :
    check [(0, ⟨[⟨[1], []⟩], []⟩), (1, ⟨[⟨[99], []⟩], []⟩)] [1]
      (fun | 0 => some [1] | _ => none) = true := by decide

end Jihoo.Initialization.Examples
