import Jihoo.ReferenceCfgEmbedding

/-! Direct first-order calls. There is one shared heap in State.frame;
suspended callers retain locals/control, never heap snapshots. Internal calls
return unit; legacy scalar returns remain top-level. Native ABI and closures
are outside this model. -/
namespace Jihoo.ReferenceCalls
open ReferenceCfg

structure Call where
  function : Nat
  arguments : Array Operand
  destination : Place
  continuation : Nat
  deriving DecidableEq, Repr
inductive Exit where
  | call (call : Call)
  | retUnit
  deriving DecidableEq, Repr
structure Code where
  base : ReferenceCfg.Code
  exits : Array (Option Exit) := #[]
  deriving DecidableEq, Repr
structure Function where
  code : Code
  parameters : Array Nat := #[]
  deriving DecidableEq, Repr
abbrev Program := Array Function
structure Continuation where
  function : Nat
  block : Nat
  locals : Array (Option Value)
  destination : Place
  deriving DecidableEq, Repr
structure State where
  function : Nat
  frame : Frame
  stack : List Continuation := []
  deriving DecidableEq, Repr
inductive Machine where
  | running (state : State)
  | returned (value : Value) (state : State)
  deriving DecidableEq, Repr
structure Next where
  machine : Machine
  events : List Event
  deriving DecidableEq, Repr
structure Outcome where
  value : Value
  state : State
  events : List Event
  deriving DecidableEq, Repr

def stackDepth (s : State) : Nat := s.stack.length

/-- Overrides replace only an actual terminator, never a statement or bad PC. -/
def extension (c : Code) (f : Frame) : Option Exit :=
  match ReferenceCfg.fetch c.base f with
  | some (.term _) => (c.exits[f.block]?).join
  | _ => none

def bindArguments (c : ReferenceCfg.Code) : List Nat → List Value → Frame → Option Frame
  | [], [], f => some f
  | slot :: slots, v :: values, f => do
      let f ← ReferenceCfg.write c f ⟨slot, false⟩ v
      bindArguments c slots values f
  | _, _, _ => none

/-- Evaluate arguments in the caller, then bind typed, distinct callee slots.
Reference provenance is transported unchanged, not dereferenced or forged. -/
def enter (p : Program) (s : State) (call : Call) : Option State := do
  let caller ← p[s.function]?
  let callee ← p[call.function]?
  if call.continuation ≥ caller.code.base.blocks.size then none else do
  if call.destination.deref then none else do
  if caller.code.base.locals[call.destination.slot]? != some .unit then none else do
  if call.destination.slot ≥ s.frame.locals.size then none else do
  if callee.parameters.toList.Nodup then do
    let values ← call.arguments.toList.mapM (ReferenceCfg.operand s.frame)
    let fresh := { ReferenceCfg.initial callee.code.base with heap := s.frame.heap }
    let frame ← bindArguments callee.code.base callee.parameters.toList values fresh
    pure ⟨call.function, frame,
      ⟨s.function, call.continuation, s.frame.locals, call.destination⟩ :: s.stack⟩
  else none

/-- Resume saved locals with the current heap, including callee writes/frees. -/
def leave (p : Program) (s : State) : Option Machine :=
  match s.stack with
  | [] => some (.returned .unit s)
  | k :: rest => do
      let caller ← p[k.function]?
      if k.block ≥ caller.code.base.blocks.size then none else do
      let frame : Frame := ⟨k.block, 0, k.locals, s.frame.heap⟩
      let frame ← ReferenceCfg.write caller.code.base frame k.destination .unit
      pure (.running ⟨k.function, frame, rest⟩)

/-- A scalar return cannot satisfy an internal unit-return contract. -/
def liftLegacy (s : State) (n : ReferenceCfg.Next) : Option Next :=
  match n.machine with
  | .running f => some ⟨.running {s with frame := f}, n.events⟩
  | .returned v f =>
      match s.stack with
      | [] => some ⟨.returned (.i64 v) {s with frame := f}, n.events⟩
      | _ :: _ => none

def tick (p : Program) (s : State) : Option Next := do
  let fn ← p[s.function]?
  match extension fn.code s.frame with
  | some (.call call) => do pure ⟨.running (← enter p s call), []⟩
  | some .retUnit => do pure ⟨← leave p s, []⟩
  | none => do liftLegacy s (← ReferenceCfg.tick fn.code.base s.frame)

/-- Independent relational rules, reusing the old CFG relation. -/
inductive Step (p : Program) : Machine → List Event → Machine → Prop where
  | legacy : p[s.function]? = some fn → extension fn.code s.frame = none →
      ReferenceCfg.Step fn.code.base (.running s.frame) es m →
      liftLegacy s ⟨m, es⟩ = some ⟨target, es⟩ → Step p (.running s) es target
  | call : p[s.function]? = some fn → extension fn.code s.frame = some (.call call) →
      enter p s call = some target → Step p (.running s) [] (.running target)
  | retUnit : p[s.function]? = some fn → extension fn.code s.frame = some .retUnit →
      leave p s = some target → Step p (.running s) [] target

theorem tick_sound (h : tick p s = some n) : Step p (.running s) n.events n.machine := by
  cases hf : p[s.function]? with
  | none => simp [tick, hf] at h
  | some fn =>
    cases he : extension fn.code s.frame with
    | none =>
      cases ht : ReferenceCfg.tick fn.code.base s.frame with
      | none => simp [tick, hf, he, ht] at h
      | some old =>
        have hl : liftLegacy s old = some n := by simpa [tick, hf, he, ht] using h
        have events : old.events = n.events := by
          cases old with
          | mk m es =>
            cases m with
            | running f =>
              simp only [liftLegacy, Option.some.injEq] at hl
              exact congrArg Next.events hl
            | returned v f =>
              cases hs : s.stack <;> simp [liftLegacy, hs] at hl
              exact congrArg Next.events hl
        have step := Step.legacy hf he (ReferenceCfg.tick_sound ht)
          (show liftLegacy s ⟨old.machine, old.events⟩ = some ⟨n.machine, old.events⟩ from by
            conv => rhs; rw [events]
            exact hl)
        simpa only [events] using step
    | some ex => cases ex with
      | call call =>
        cases hc : enter p s call <;> simp [tick, hf, he, hc] at h
        subst n
        exact .call hf he hc
      | retUnit =>
        cases hr : leave p s <;> simp [tick, hf, he, hr] at h
        subst n
        exact .retUnit hf he hr

theorem tick_complete (h : Step p (.running s) es target) : tick p s = some ⟨target, es⟩ := by
  cases h with
  | legacy hf he hs hl => simp [tick, hf, he, ReferenceCfg.tick_complete hs, hl]
  | call hf he hc => simp [tick, hf, he, hc]
  | retUnit hf he hr => simp [tick, hf, he, hr]

theorem Step.deterministic (a : Step p m es n) (b : Step p m fs t) : es = fs ∧ n = t := by
  cases m with
  | returned _ _ => cases a
  | running s =>
    have h := (tick_complete a).symm.trans (tick_complete b)
    cases Option.some.inj h
    exact ⟨rfl, rfl⟩

inductive Steps (p : Program) : Machine → List Event → Machine → Prop where
  | nil : Steps p m [] m
  | cons : Step p m first mid → Steps p mid rest finish → Steps p m (first ++ rest) finish

/-- One fuel per statement/terminator, including call and return. Fuel is
never reset on entry and is distinct from the observable stackDepth. -/
def execute : Nat → Program → State → Option Outcome
  | 0, _, _ => none
  | fuel + 1, p, s => do
      let n ← tick p s
      match n.machine with
      | .returned value state => pure ⟨value, state, n.events⟩
      | .running state => do
          let out ← execute fuel p state
          pure {out with events := n.events ++ out.events}

theorem execute_sound (h : execute fuel p s = some out) :
    Steps p (.running s) out.events (.returned out.value out.state) := by
  induction fuel generalizing s out with
  | zero => simp [execute] at h
  | succ fuel ih =>
    cases hn : tick p s with
    | none => simp [execute, hn] at h
    | some n =>
      have hs := tick_sound hn
      cases hm : n.machine with
      | returned v t =>
        simp [execute, hn, hm] at h
        subst out
        simpa using Steps.cons (hm ▸ hs) Steps.nil
      | running t =>
        cases hr : execute fuel p t with
        | none => simp [execute, hn, hm, hr] at h
        | some result =>
          simp [execute, hn, hm, hr] at h
          subst out
          exact .cons (hm ▸ hs) (ih hr)

def embedCode (c : ReferenceCfg.Code) : Code := ⟨c, #[]⟩
def embedProgram (c : ReferenceCfg.Code) : Program := #[⟨embedCode c, #[]⟩]
def embedState (f : Frame) : State := ⟨0, f, []⟩
def embedMachine : ReferenceCfg.Machine → Machine
  | .running f => .running (embedState f)
  | .returned v f => .returned (.i64 v) (embedState f)
def embedNext (n : ReferenceCfg.Next) : Next := ⟨embedMachine n.machine, n.events⟩
def embedOutcome (out : ReferenceCfg.Outcome) : Outcome :=
  ⟨.i64 out.value, embedState out.frame, out.events⟩

@[simp] theorem extension_embed (c f) : extension (embedCode c) f = none := by
  simp only [extension, embedCode]
  cases ReferenceCfg.fetch c f with
  | none => rfl
  | some i => cases i <;> simp

/-- Exact Option equality preserves stuck transitions as well as successes. -/
theorem tick_embed (c f) : tick (embedProgram c) (embedState f) =
    (ReferenceCfg.tick c f).map embedNext := by
  simp [tick, embedProgram, embedState]
  change (ReferenceCfg.tick c f).bind (liftLegacy (embedState f)) = _
  cases ReferenceCfg.tick c f with
  | none => rfl
  | some n => cases n with
    | mk m es => cases m <;> rfl

/-- All fuel budgets, events and final locals/control/heap are preserved. -/
theorem execute_embed (fuel c f) : execute fuel (embedProgram c) (embedState f) =
    (ReferenceCfg.execute fuel c f).map embedOutcome := by
  induction fuel generalizing f with
  | zero => rfl
  | succ fuel ih =>
    simp only [execute, ReferenceCfg.execute, tick_embed]
    cases ht : ReferenceCfg.tick c f with
    | none => rfl
    | some n =>
      cases hm : n.machine with
      | returned v g => simp [embedNext, embedMachine, hm, embedOutcome]
      | running g =>
        simp [embedNext, embedMachine, hm, ih]
        cases ReferenceCfg.execute fuel c g <;> rfl

/-- Composition with #193 preserves the existing BoundedMir embedding. -/
theorem execute_scalar (fuel c f) :
    execute fuel (embedProgram (ReferenceCfg.Scalar.code c))
      (embedState (ReferenceCfg.Scalar.frame f)) =
    (BoundedMir.execute fuel c f).map (embedOutcome ∘ ReferenceCfg.Scalar.outcome) := by
  rw [execute_embed, ReferenceCfg.Scalar.execute_eq, Option.map_map]


/-- Local argument binding cannot change the shared heap. -/
theorem bindArguments_heap (h : bindArguments c slots values f = some g) : g.heap = f.heap := by
  induction slots generalizing values f with
  | nil => cases values <;> simp [bindArguments] at h; subst g; rfl
  | cons slot slots ih =>
    cases values with
    | nil => simp [bindArguments] at h
    | cons v values =>
      simp only [bindArguments, bind, Option.bind_eq_some_iff] at h
      obtain ⟨next, hw, rest⟩ := h
      have heap : next.heap = f.heap := by
        unfold ReferenceCfg.write at hw
        cases ht : c.locals[slot]? <;> simp [ht] at hw
        exact (congrArg Frame.heap hw.2).symm
      exact (ih rest).trans heap

theorem enter_stack_heap (h : enter p s call = some t) :
    t.stack = ⟨s.function, call.continuation, s.frame.locals, call.destination⟩ :: s.stack ∧
    t.function = call.function ∧ t.frame.heap = s.frame.heap := by
  simp only [enter, bind, Option.bind_eq_some_iff] at h
  obtain ⟨caller, _, callee, _, h⟩ := h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨values, _, frame, hb, rfl⟩ := h
  have hh := bindArguments_heap hb
  exact ⟨rfl, rfl, hh⟩

theorem enter_depth (h : enter p s call = some t) : stackDepth t = stackDepth s + 1 := by
  simp [stackDepth, (enter_stack_heap h).1]

/-- Unit cannot be stored through a heap pointer; successful unit writes are
local updates and preserve the current heap. -/
theorem write_unit_heap (h : ReferenceCfg.write c f dest .unit = some g) :
    g.heap = f.heap := by
  cases ht : c.locals[dest.slot]? with
  | none => simp [ReferenceCfg.write, ht] at h
  | some ty =>
    cases hd : dest.deref with
    | false =>
      simp [ReferenceCfg.write, ht, hd] at h
      exact (congrArg Frame.heap h.2).symm
    | true =>
      cases hv : (f.locals[dest.slot]?).join with
      | none => simp [ReferenceCfg.write, ht, hd, hv] at h
      | some v => cases v <;> simp [ReferenceCfg.write, ht, hd, hv] at h

theorem leave_stack_heap (hs : s.stack = k :: rest) (h : leave p s = some (.running t)) :
    t.stack = rest ∧ t.function = k.function ∧ t.frame.heap = s.frame.heap := by
  simp only [leave, hs, bind, Option.bind_eq_some_iff] at h
  obtain ⟨caller, _, h⟩ := h
  split at h <;> try contradiction
  simp only [pure, Option.bind_eq_some_iff, Option.some.injEq, Machine.running.injEq] at h
  obtain ⟨frame, hw, rfl⟩ := h
  have hh := write_unit_heap hw
  exact ⟨rfl, rfl, hh⟩

theorem leave_depth (hs : s.stack = k :: rest) (h : leave p s = some (.running t)) :
    stackDepth s = stackDepth t + 1 := by
  simp [stackDepth, hs, (leave_stack_heap hs h).1]

/-- Both directions preserve every finite prefix, including stuck programs. -/
theorem step_embed (h : ReferenceCfg.Step c m es n) :
    Step (embedProgram c) (embedMachine m) es (embedMachine n) := by
  cases m with
  | returned v f => cases h
  | running f =>
    have ht : tick (embedProgram c) (embedState f) = some ⟨embedMachine n, es⟩ := by
      rw [tick_embed, ReferenceCfg.tick_complete h]
      rfl
    exact tick_sound ht

theorem step_reflect (h : Step (embedProgram c) (embedMachine m) es target) :
    ∃ n, ReferenceCfg.Step c m es n ∧ target = embedMachine n := by
  cases m with
  | returned v f => cases h
  | running f =>
    have ht := tick_complete h
    rw [tick_embed] at ht
    cases hb : ReferenceCfg.tick c f with
    | none => simp [hb] at ht
    | some n =>
      simp only [hb, Option.map_some, Option.some.injEq] at ht
      have he := congrArg Next.events ht
      have hm := congrArg Next.machine ht
      change n.events = es at he
      change embedMachine n.machine = target at hm
      exact ⟨n.machine, he ▸ ReferenceCfg.tick_sound hb, hm.symm⟩

theorem steps_embed (h : ReferenceCfg.Steps c m es n) :
    Steps (embedProgram c) (embedMachine m) es (embedMachine n) := by
  induction h with
  | nil => exact .nil
  | cons head _ ih => exact .cons (step_embed head) ih

theorem steps_reflect (h : Steps (embedProgram c) (embedMachine m) es target) :
    ∃ n, ReferenceCfg.Steps c m es n ∧ target = embedMachine n := by
  generalize hs : embedMachine m = start at h
  induction h generalizing m with
  | nil => exact ⟨m, .nil, hs.symm⟩
  | cons head tail ih =>
    rw [← hs] at head
    obtain ⟨mid, oldHead, eq⟩ := step_reflect head
    obtain ⟨finish, oldTail, eqFinish⟩ := ih eq.symm
    exact ⟨finish, .cons oldHead oldTail, eqFinish⟩

end Jihoo.ReferenceCalls
