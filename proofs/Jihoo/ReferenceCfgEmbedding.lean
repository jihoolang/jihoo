import Jihoo.ReferenceCfg
import Jihoo.BoundedMirExecutionAdequacy

/-! Exact scalar conservativity, including failure, arbitrary initial heaps,
and every intermediate state. No well-formedness premise is needed. -/
namespace Jihoo.ReferenceCfg
namespace Scalar
abbrev B := BoundedMir.Code

abbrev value := embedValue

def rhs : BoundedMir.Rvalue → Rvalue
  | .use a => .use a | .bin op a b => .bin op a b
  | .ptrCast a => .ptrCast a | .offset a b => .offset a b

def stmt (s : BoundedMir.Stmt) : Stmt := ⟨s.place, rhs s.value⟩
def block (b : BoundedMir.Block) : Block := ⟨b.statements.map stmt, b.term⟩
def code (c : BoundedMir.Code) : Code := ⟨c.locals, c.blocks.map block⟩
def frame (f : BoundedMir.Frame) : Frame :=
  ⟨f.block, f.index, f.locals.map (Option.map value), ReferenceHeap.embed f.heap⟩
def machine : BoundedMir.Machine → Machine
  | .running f => .running (frame f)
  | .returned v f => .returned v (frame f)
def next (n : BoundedMir.Next) : Next := ⟨machine n.machine, n.events⟩
def outcome (o : BoundedMir.Outcome) : Outcome := ⟨o.value, frame o.frame, o.events⟩
def instruction : BoundedMir.Instruction → Instruction
  | .stmt s => .stmt (stmt s) | .term t => .term t

@[simp] theorem value_type (v) : valueType (value v) = BoundedMir.valueType v := by cases v <;> rfl
@[simp] theorem constant_eq (c) : constant c = (BoundedMir.constant c).map value := rfl

@[simp] theorem locals_get (f : BoundedMir.Frame) (i : Nat) :
    ((frame f).locals[i]?).join = ((f.locals[i]?).join).map value := by
  cases h : f.locals[i]? with
  | none => simp [frame, h]
  | some v => cases v <;> simp [frame, h, value]

@[simp] theorem load_eq (H : Array BoundedMir.Object) (j i) :
    load (ReferenceHeap.embed H) j i = (BoundedMir.load H j i).map Value.i64 := by
  simp only [load, ReferenceHeap.load, ReferenceHeap.address, ReferenceHeap.embed, Array.getElem?_map]
  cases h : H[j]? with
  | none => simp [h, BoundedMir.load]
  | some obj =>
    by_cases live : obj.alive = true
    · by_cases bound : i < obj.cells.size
      · simp [ReferenceHeap.embedObject, live, bound, BoundedMir.load, h]
        cases obj.cells[i] <;> rfl
      · simp [ReferenceHeap.embedObject, live, bound, BoundedMir.load, h]
    · have dead : obj.alive = false := Bool.eq_false_iff.mpr live
      simp [ReferenceHeap.embedObject, dead, BoundedMir.load, h]

@[simp] theorem operand_eq (f) (op) :
    operand (frame f) op = (BoundedMir.operand f op).map value := by
  cases op with
  | constant c => exact constant_eq c
  | copy p =>
    simp only [operand, BoundedMir.operand, locals_get]
    cases h : (f.locals[p.slot]?).join with
    | none => simp
    | some v =>
      cases p.deref <;> cases v <;> simp [value, embedValue, frame, load_eq]
      cases BoundedMir.load f.heap _ _ <;> rfl

@[simp] theorem binary_eq (op) (a b) :
    binary op (value a) (value b) = (BoundedMir.binary op a b).map value := by
  cases a <;> cases b <;> rfl

@[simp] theorem rvalue_eq (f) (r) :
    rvalue (frame f) (rhs r) = (BoundedMir.rvalue f r).map value := by
  cases r with
  | use a => exact operand_eq f a
  | bin op a b =>
    simp only [rhs, rvalue, BoundedMir.rvalue, operand_eq]
    cases BoundedMir.operand f a <;> cases BoundedMir.operand f b <;> simp [binary_eq]
  | ptrCast a =>
    simp only [rhs, rvalue, BoundedMir.rvalue, operand_eq]
    cases BoundedMir.operand f a with
    | none => rfl
    | some v =>
      cases v <;> simp [value, embedValue, frame, ReferenceHeap.embed]
      rename_i j i
      cases f.heap[j]? <;> simp [ReferenceHeap.embedObject] <;> split <;> rfl
  | offset a b =>
    simp only [rhs, rvalue, BoundedMir.rvalue, operand_eq]
    cases BoundedMir.operand f a with
    | none => rfl
    | some v =>
      cases v <;> simp [value, embedValue]
      cases BoundedMir.operand f b with
      | none => rfl
      | some w =>
        cases w <;> simp [value, embedValue, frame, ReferenceHeap.embed]
        rename_i j i n
        cases f.heap[j]? <;> simp [ReferenceHeap.embedObject] <;> split <;> rfl

@[simp] theorem write_eq (c f) (p : Place) (v) :
    write (code c) (frame f) p (value v) = (BoundedMir.write c f p v).map frame := by
  simp only [write, BoundedMir.write, code, locals_get]
  cases ht : c.locals[p.slot]? with
  | none => simp
  | some ty =>
    cases hd : p.deref with
    | false => simp [value_type, frame]
    | true =>
      simp only [↓reduceIte]
      by_cases hty : ty = .ptr
      · subst ty
        cases hv : (f.locals[p.slot]?).join with
        | none => simp
        | some w =>
          cases w <;> simp [value, embedValue]
          rename_i j i
          cases v <;> simp
          rename_i n
          cases ho : f.heap[j]? with
          | none => simp [ReferenceHeap.store, ReferenceHeap.address, frame, ReferenceHeap.embed, ho]
          | some obj =>
            by_cases live : obj.alive = true
            · by_cases bound : i < obj.cells.size
              · by_cases payload : n < BoundedMir.scalarBound
                · simp [ReferenceHeap.store, ReferenceHeap.address, ReferenceHeap.validCell,
                    frame, ReferenceHeap.embed, ReferenceHeap.embedObject, ho, live, bound,
                    payload]
                · simp [ReferenceHeap.store, ReferenceHeap.address, ReferenceHeap.validCell,
                    frame, ReferenceHeap.embed, ReferenceHeap.embedObject, ho, live, bound,
                    payload]
              · simp [ReferenceHeap.store, ReferenceHeap.address, frame, ReferenceHeap.embed,
                  ReferenceHeap.embedObject, ho, live, bound]
            · have dead : obj.alive = false := Bool.eq_false_iff.mpr live
              simp [ReferenceHeap.store, ReferenceHeap.address, frame, ReferenceHeap.embed,
                ReferenceHeap.embedObject, ho, dead]
      · simp [hty]

@[simp] theorem fetch_eq (c f) :
    fetch (code c) (frame f) = (BoundedMir.fetch c f).map instruction := by
  simp only [fetch, code, frame, Array.getElem?_map, BoundedMir.fetch]
  cases c.blocks[f.block]? with
  | none => rfl
  | some b =>
    simp [block]
    split
    · simp [instruction, Option.map_map, Function.comp_def]
    · split <;> simp [instruction]

@[simp] theorem switch_eq (v) : switchValue (value v) = BoundedMir.switchValue v := by
  cases v <;> try rfl
  rename_i b
  cases b <;> rfl
@[simp] theorem advance_eq (f) : advance (frame f) = frame (BoundedMir.advance f) := rfl
@[simp] theorem jump_eq (f b) : jump (frame f) b = frame (BoundedMir.jump f b) := rfl
@[simp] theorem heap_update (f H) :
    {frame f with heap := ReferenceHeap.embed H} = frame {f with heap := H} := rfl
@[simp] theorem heap_size (f) : (frame f).heap.size = f.heap.size := by
  simp [frame, ReferenceHeap.embed]
@[simp] theorem block_size (c) : (code c).blocks.size = c.blocks.size := by simp [code]
@[simp] theorem alloc_eq (f bytes) :
    mallocHeap (frame f).heap bytes = (BoundedMir.mallocHeap f.heap bytes).map ReferenceHeap.embed :=
  ReferenceHeap.allocate_compatible f.heap
@[simp] theorem free_eq (f j i) :
    freeHeap (frame f).heap j i = (BoundedMir.freeHeap f.heap j i).map ReferenceHeap.embed :=
  ReferenceHeap.release_compatible f.heap

/-- Exact one-instruction behavior, including all stuck cases. -/
theorem tick_eq (c f) :
    tick (code c) (frame f) = (BoundedMir.tick c f).map next := by
  rw [tick_eq_rawTick, BoundedMir.tick_eq_rawTick]
  unfold rawTick BoundedMir.rawTick
  rw [fetch_eq]
  cases hf : BoundedMir.fetch c f with
  | none => rfl
  | some ins => cases ins with
    | stmt st =>
      cases st with | mk p r =>
        simp only [instruction, stmt, Option.map_some, rvalue_eq]
        cases hv : BoundedMir.rvalue f r with
        | none => rfl
        | some v =>
          simp only [Option.map_some, write_eq]
          cases BoundedMir.write c f p v <;> simp [next, machine]
    | term t =>
      cases t with
      | goto b => simp [instruction, next, machine, apply_ite]
      | switch op cs other =>
        simp only [instruction, Option.map_some, operand_eq]
        cases BoundedMir.operand f op with
        | none => rfl
        | some v =>
          simp only [Option.map_some, switch_eq]
          cases BoundedMir.switchValue v with
          | none => rfl
          | some n =>
            simp only [show select = BoundedMir.select from rfl, block_size]
            by_cases hb : BoundedMir.select n cs other < c.blocks.size <;>
              simp [hb, next, machine]
      | assert op b =>
        simp only [instruction, Option.map_some, operand_eq]
        cases BoundedMir.operand f op with
        | none => simp
        | some v =>
          cases v <;> simp [value, embedValue]
          rename_i test
          cases test <;> simp [next, machine]
      | malloc op dest b =>
        simp only [instruction, Option.map_some, operand_eq]
        cases BoundedMir.operand f op with
        | none => rfl
        | some v =>
          cases v <;> simp only [value, embedValue, Option.map_some]
          all_goals try rfl
          rw [alloc_eq]
          cases BoundedMir.mallocHeap f.heap _ with
          | none => rfl
          | some H =>
            simp only [Option.map_some, heap_update, heap_size]
            rw [show Value.pointer f.heap.size 0 = value (.pointer f.heap.size 0) from rfl, write_eq]
            cases BoundedMir.write c {f with heap := H} dest (.pointer f.heap.size 0) <;>
              simp [next, machine, apply_ite]
      | free op dest b =>
        simp only [instruction, Option.map_some, operand_eq]
        cases BoundedMir.operand f op with
        | none => rfl
        | some v =>
          cases v <;> simp only [value, embedValue, Option.map_some]
          all_goals try rfl
          rw [free_eq]
          cases BoundedMir.freeHeap f.heap _ _ with
          | none => rfl
          | some H =>
            simp only [Option.map_some, heap_update]
            rw [show Value.unit = value .unit from rfl, write_eq]
            cases BoundedMir.write c {f with heap := H} dest .unit <;>
              simp [next, machine, apply_ite]
      | ret =>
        simp only [instruction, Option.map_some, locals_get]
        cases (f.locals[(0 : Nat)]?).join with
        | none => rfl
        | some v => cases v <;> rfl

/-- Every old relational transition has exactly the same event trace. -/
theorem step_forward (h : BoundedMir.Step c m es n) :
    Step (code c) (machine m) es (machine n) := by
  cases m with
  | returned v f => cases h
  | running f =>
    have ht := BoundedMir.tick_complete h
    have he : tick (code c) (frame f) = some ⟨machine n, es⟩ := by
      simp [tick_eq, ht, next]
    exact tick_sound he

/-- No new reference transition can escape the embedded scalar state. -/
theorem step_reflect (h : Step (code c) (machine m) es target) :
    ∃ n, BoundedMir.Step c m es n ∧ target = machine n := by
  cases m with
  | returned v f => cases h
  | running f =>
    have ht := tick_complete h
    rw [tick_eq] at ht
    cases hb : BoundedMir.tick c f with
    | none => simp [hb] at ht
    | some n =>
      simp only [hb, Option.map_some, Option.some.injEq] at ht
      have he := congrArg Next.events ht
      have hm := congrArg Next.machine ht
      change n.events = es at he
      change machine n.machine = target at hm
      exact ⟨n.machine, he ▸ BoundedMir.tick_sound hb, hm.symm⟩

theorem steps_forward (h : BoundedMir.Steps c m es n) :
    Steps (code c) (machine m) es (machine n) := by
  induction h with
  | nil => exact .nil
  | cons head _ ih => exact .cons (step_forward head) ih

/-- All finite prefixes, including stuck and nonterminating executions, remain
in the image of the old semantics; the exact old heap is retained. -/
theorem steps_reflect (h : Steps (code c) (machine m) es target) :
    ∃ n, BoundedMir.Steps c m es n ∧ target = machine n := by
  generalize hs : machine m = start at h
  induction h generalizing m with
  | nil => exact ⟨m, .nil, hs.symm⟩
  | cons head tail ih =>
    rw [← hs] at head
    obtain ⟨mid, oldHead, eq⟩ := step_reflect head
    obtain ⟨finish, oldTail, eqFinish⟩ := ih eq.symm
    exact ⟨finish, .cons oldHead oldTail, eqFinish⟩

/-- Scalar-only code and initial states are the images of BoundedMir data.
This includes scalar heap pointers and nonnull tags, but excludes null and
reference words. This predicate requires no termination or validity premise. -/
def InScalar (m : Machine) : Prop := ∃ old, m = machine old

theorem scalar_invariant (start : InScalar m) (run : Steps (code c) m es n) : InScalar n := by
  obtain ⟨old, rfl⟩ := start
  obtain ⟨finish, _, eq⟩ := steps_reflect run
  exact ⟨finish, eq⟩

/-- Fuel is unchanged: one unit per statement/terminator, including return.
Equality of Options also preserves failure at every insufficient fuel budget. -/
theorem execute_eq (fuel c f) :
    execute fuel (code c) (frame f) = (BoundedMir.execute fuel c f).map outcome := by
  induction fuel generalizing f with
  | zero => rfl
  | succ fuel ih =>
    simp only [execute, BoundedMir.execute, tick_eq]
    cases ht : BoundedMir.tick c f with
    | none => rfl
    | some n =>
      cases hm : n.machine with
      | returned v g => simp [next, machine, hm, outcome]
      | running g =>
        simp [next, hm, machine, ih]
        cases BoundedMir.execute fuel c g <;> rfl

@[simp] theorem initial_eq (c) : initial (code c) = frame (BoundedMir.initial c) := by
  simp [initial, code, frame, BoundedMir.initial, ReferenceHeap.embed, Array.map_replicate]
@[simp] theorem heap_empty_eq (f) : heapEmpty (frame f) = BoundedMir.heapEmpty f := by
  simp [heapEmpty, BoundedMir.heapEmpty, frame, ReferenceHeap.embed, ReferenceHeap.embedObject, Function.comp_def]

/-- Existing valid-code, fuel and no-live-heap admission evidence transfers
without changing the old admission predicate or any SizedMir theorem. -/
theorem accepted_execution (a : BoundedMir.Accepted c) :
    execute a.fuel (code c) (initial (code c)) = some (outcome a.outcome) := by
  rw [initial_eq, execute_eq, a.execution]
  rfl

theorem accepted_all_returns (a : BoundedMir.Accepted c)
    (run : Steps (code c) (.running (initial (code c))) es (.returned v f)) :
    v = a.outcome.value ∧ f = frame a.outcome.frame ∧ es = a.outcome.events := by
  exact execute_unique (accepted_execution a) run

theorem accepted_final_heap (a : BoundedMir.Accepted c)
    (run : Steps (code c) (.running (initial (code c))) es (.returned v f)) :
    f.heap = ReferenceHeap.embed a.outcome.frame.heap ∧ heapEmpty f = true := by
  obtain ⟨_, rfl, _⟩ := accepted_all_returns a run
  exact ⟨rfl, by simpa using a.no_live_heap⟩

end Scalar
end Jihoo.ReferenceCfg
