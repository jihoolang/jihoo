import Jihoo.BoundedMir

namespace Jihoo.BoundedMir

/-- A proof-free transition evaluator for symbolic reduction. -/
def rawTick (c : Code) (f : Frame) : Option Next :=
  match fetch c f with
  | none => none
  | some (.stmt ⟨place, rhs⟩) =>
    match rvalue f rhs with
    | none => none
    | some v => match write c f place v with
      | none => none
      | some target => some ⟨.running (advance target), []⟩
  | some (.term (.goto block)) =>
    if block < c.blocks.size then some ⟨.running (jump f block), []⟩ else none
  | some (.term (.switch op cases otherwise)) =>
    match operand f op with
    | none => none
    | some v => match switchValue v with
      | none => none
      | some n => if select n cases otherwise < c.blocks.size then
          some ⟨.running (jump f (select n cases otherwise)), []⟩ else none
  | some (.term (.assert op block)) =>
    if operand f op = some (.boolean true) then
      if block < c.blocks.size then some ⟨.running (jump f block), []⟩ else none
    else none
  | some (.term (.malloc op dest block)) =>
    match operand f op with
    | some (.u64 bytes) => match mallocHeap f.heap bytes with
      | none => none
      | some heap => match write c {f with heap := heap} dest (.pointer f.heap.size 0) with
        | none => none
        | some target => if block < c.blocks.size then
            some ⟨.running (jump target block), [.alloc f.heap.size bytes]⟩ else none
    | _ => none
  | some (.term (.free op dest block)) =>
    match operand f op with
    | some (.pointer object index) => match freeHeap f.heap object index with
      | none => none
      | some heap => match write c {f with heap := heap} dest .unit with
        | none => none
        | some target => if block < c.blocks.size then
            some ⟨.running (jump target block), [.free object]⟩ else none
    | _ => none
  | some (.term .ret) =>
    match (f.locals[(0 : Nat)]?).join with
    | some (.i64 v) => some ⟨.returned v f, []⟩
    | _ => none

theorem tick_eq_rawTick (c : Code) (f : Frame) : tick c f = rawTick c f := by
  unfold tick next rawTick
  repeat' first | (solve | simp_all) | split

theorem rawTick_sound (h : rawTick c f = some result) :
    Step c (.running f) result.events result.machine := by
  apply tick_sound
  rw [tick_eq_rawTick]
  exact h

/-- A finite instruction prefix, stopping unchanged at a returned machine. -/
def runFor : Nat → Code → Machine → Option Next
  | 0, _, m => some ⟨m, []⟩
  | _ + 1, _, .returned v f => some ⟨.returned v f, []⟩
  | fuel + 1, c, .running f => do
    let next ← rawTick c f
    let rest ← runFor fuel c next.machine
    return ⟨rest.machine, next.events ++ rest.events⟩

theorem runFor_sound (h : runFor fuel c m = some out) : Steps c m out.events out.machine := by
  induction fuel generalizing m out with
  | zero => simp [runFor] at h; subst out; exact .nil
  | succ fuel ih =>
    cases m with
    | returned v f => simp [runFor] at h; subst out; exact .nil
    | running f =>
      cases ht : rawTick c f with
      | none => simp [runFor, ht] at h
      | some next =>
        cases hr : runFor fuel c next.machine with
        | none => simp [runFor, ht, hr] at h
        | some rest =>
          simp [runFor, ht, hr] at h
          subst out
          exact .cons (rawTick_sound ht) (ih hr)

theorem steps_trans (first : Steps c a es b) (rest : Steps c b fs d) :
    Steps c a (es ++ fs) d := by
  induction first with
  | nil => exact rest
  | cons head _ ih => simpa [List.append_assoc] using Steps.cons head (ih rest)

end Jihoo.BoundedMir
