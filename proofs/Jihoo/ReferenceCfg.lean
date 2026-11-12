import Jihoo.ReferenceHeap

/-! An abstract reference-cell CFG extension. The old scalar CFG is embedded
constructor by constructor; native encoding, calls, reuse and full compiler
correctness are outside this milestone. ptrCast remains a nonnull tag. -/
namespace Jihoo.ReferenceCfg

abbrev Event := HeapLifecycle.Event

def wordBound : Nat := 2^64
def scalarBound : Nat := 2^63

abbrev Ty := BoundedMir.Ty
inductive Value where
  | i64 (n : Nat) | u64 (n : Nat) | boolean (b : Bool)
  | pointer (object index : Nat)
  | address (object : Nat)
  | unit
  | null
  | referenceWord (reference : ReferenceHeap.Ref)
  deriving DecidableEq, Repr
abbrev Constant := BoundedMir.Constant
abbrev Place := BoundedMir.Place
abbrev Operand := BoundedMir.Operand
abbrev Bin := BoundedMir.Bin
inductive Rvalue where
  | use (operand : Operand)
  | bin (op : Bin) (left right : Operand)
  | ptrCast (operand : Operand)
  | offset (pointer index : Operand)
  | null
  | nullTest (pointer : Operand)
  | pointerToWord (pointer : Operand)
  | wordToPointer (word : Operand)
  deriving DecidableEq, Repr
structure Stmt where
  place : Place
  value : Rvalue
  deriving DecidableEq, Repr
abbrev Term := BoundedMir.Term
structure Block where
  statements : Array Stmt
  term : Term
  deriving DecidableEq, Repr
structure Code where
  locals : Array Ty
  blocks : Array Block
  deriving DecidableEq, Repr
abbrev Object := ReferenceHeap.Object
structure Frame where
  block : Nat
  index : Nat
  locals : Array (Option Value)
  heap : Array Object
  deriving DecidableEq, Repr
inductive Machine where
  | running (frame : Frame)
  | returned (value : Nat) (frame : Frame)
  deriving DecidableEq, Repr
structure Next where
  machine : Machine
  events : List Event
  deriving DecidableEq, Repr
structure Outcome where
  value : Nat
  frame : Frame
  events : List Event
  deriving DecidableEq, Repr

def valueType : Value → Ty
  | .i64 _ => .i64 | .u64 _ | .address _ => .u64 | .boolean _ => .bool
  | .pointer _ _ | .null => .ptr | .unit => .unit
  | .referenceWord _ => .i64

def embedValue : BoundedMir.Value → Value
  | .i64 n => .i64 n | .u64 n => .u64 n | .boolean b => .boolean b
  | .pointer j i => .pointer j i | .address j => .address j | .unit => .unit

/-- Only the old scalar fragment supports arithmetic; provenance words are
not integers and cannot participate in integer arithmetic or forge addresses. -/
def scalarValue : Value → Option BoundedMir.Value
  | .i64 n => some (.i64 n) | .u64 n => some (.u64 n)
  | .boolean b => some (.boolean b) | .pointer j i => some (.pointer j i)
  | .address j => some (.address j) | .unit => some .unit
  | .null | .referenceWord _ => none

def constant (c : Constant) : Option Value := (BoundedMir.constant c).map embedValue

def load (heap : ReferenceHeap.Heap) (object index : Nat) : Option Value := do
  match ← ReferenceHeap.load heap (.object object index) with
  | .scalar n => pure (.i64 n)
  | .reference r => pure (.referenceWord r)

def toRef : Value → Option ReferenceHeap.Ref
  | .pointer j i => some (.object j i)
  | .null => some .null
  | _ => none

def ofRef : ReferenceHeap.Ref → Value
  | .object j i => .pointer j i
  | .null => .null

def operand (f : Frame) : Operand → Option Value
  | .constant c => constant c
  | .copy place => do
    let v ← (f.locals[place.slot]?).join
    if place.deref then
      let .pointer object index := v | none
      load f.heap object index
    else pure v

def binary (op : Bin) (a b : Value) : Option Value := do
  let a ← scalarValue a
  let b ← scalarValue b
  (BoundedMir.binary op a b).map embedValue

def rvalue (f : Frame) : Rvalue → Option Value
  | .use op => operand f op
  | .bin op a b => do binary op (← operand f a) (← operand f b)
  | .ptrCast a => do
    let .pointer object index ← operand f a | none
    let obj ← f.heap[object]?
    if obj.alive && index == 0 then some (.address object) else none
  | .offset a b => do
    let .pointer object index ← operand f a | none
    let .u64 offset ← operand f b | none
    let obj ← f.heap[object]?
    if obj.alive && index + offset ≤ obj.cells.size then some (.pointer object (index + offset)) else none

  | .null => some .null
  | .nullTest op => do pure (.boolean (ReferenceHeap.isNull (← toRef (← operand f op))))
  | .pointerToWord op => do pure (.referenceWord (← toRef (← operand f op)))
  | .wordToPointer op => do
    let .referenceWord r ← operand f op | none
    pure (ofRef r)

def write (c : Code) (f : Frame) (place : Place) (v : Value) : Option Frame := do
  let ty ← c.locals[place.slot]?
  if place.deref then
    if ty != .ptr then none else do
    let .pointer object index ← (f.locals[place.slot]?).join | none
    let cell ← match v with
      | .i64 n => some (ReferenceHeap.Cell.scalar n)
      | .referenceWord r => some (.reference r)
      | _ => none
    let heap ← ReferenceHeap.store f.heap (.object object index) cell
    pure { f with heap := heap }
  else if valueType v == ty && place.slot < f.locals.size then
    pure { f with locals := f.locals.set! place.slot (some v) }
  else none

abbrev mallocHeap := ReferenceHeap.allocate
def freeHeap (heap : ReferenceHeap.Heap) (object index : Nat) :=
  ReferenceHeap.release heap (.object object index)

def jump (f : Frame) (block : Nat) : Frame := { f with block := block, index := 0 }
def advance (f : Frame) : Frame := { f with index := f.index + 1 }

def switchValue : Value → Option Nat
  | .u64 n | .i64 n => some n
  | .boolean false => some 0 | .boolean true => some 1
  | _ => none

def select (n : Nat) (cases : List (Nat × Nat)) (otherwise : Nat) : Nat :=
  ((cases.find? (fun pair => pair.1 == n)).map Prod.snd).getD otherwise

inductive Instruction where
  | stmt (statement : Stmt)
  | term (term : Term)
  deriving DecidableEq, Repr

def fetch (c : Code) (f : Frame) : Option Instruction := do
  let b ← c.blocks[f.block]?
  if f.index < b.statements.size then (b.statements[f.index]?).map .stmt
  else if f.index == b.statements.size then some (.term b.term) else none

/-- Independent relational rules for actual statement/terminator transitions.
There is no reference to the executable tick or whole-program evaluator. -/
inductive Step (c : Code) : Machine → List Event → Machine → Prop where
  | assign : fetch c f = some (.stmt ⟨place, rhs⟩) → rvalue f rhs = some v → write c f place v = some next →
      Step c (.running f) [] (.running (advance next))
  | goto : fetch c f = some (.term (.goto block)) → block < c.blocks.size →
      Step c (.running f) [] (.running (jump f block))
  | switch : fetch c f = some (.term (.switch op cases otherwise)) → operand f op = some v →
      switchValue v = some n → select n cases otherwise < c.blocks.size →
      Step c (.running f) [] (.running (jump f (select n cases otherwise)))
  | assert : fetch c f = some (.term (.assert op block)) → operand f op = some (.boolean true) → block < c.blocks.size →
      Step c (.running f) [] (.running (jump f block))
  | malloc : fetch c f = some (.term (.malloc op dest block)) → operand f op = some (.u64 bytes) →
      mallocHeap f.heap bytes = some heap →
      write c {f with heap := heap} dest (.pointer f.heap.size 0) = some next → block < c.blocks.size →
      Step c (.running f) [.alloc f.heap.size bytes] (.running (jump next block))
  | free : fetch c f = some (.term (.free op dest block)) → operand f op = some (.pointer object index) →
      freeHeap f.heap object index = some heap → write c {f with heap := heap} dest .unit = some next → block < c.blocks.size →
      Step c (.running f) [.free object] (.running (jump next block))
  | ret : fetch c f = some (.term .ret) → (f.locals[(0 : Nat)]?).join = some (.i64 v) →
      Step c (.running f) [] (.returned v f)

/-- A proof-producing implementation of the independent transition rules. -/
def next (c : Code) (f : Frame) : Option {n : Next // Step c (.running f) n.events n.machine} :=
  match hf : fetch c f with
  | none => none
  | some (.stmt ⟨place, rhs⟩) =>
    match hv : rvalue f rhs with
    | none => none
    | some v => match hw : write c f place v with
      | none => none
      | some target => some ⟨⟨.running (advance target), []⟩, .assign hf hv hw⟩
  | some (.term (.goto block)) =>
    if hb : block < c.blocks.size then some ⟨⟨.running (jump f block), []⟩, .goto hf hb⟩ else none
  | some (.term (.switch op cases otherwise)) =>
    match hv : operand f op with
    | none => none
    | some v => match hn : switchValue v with
      | none => none
      | some n => if hb : select n cases otherwise < c.blocks.size then
          some ⟨⟨.running (jump f (select n cases otherwise)), []⟩, .switch hf hv hn hb⟩ else none
  | some (.term (.assert op block)) =>
    if hv : operand f op = some (.boolean true) then
      if hb : block < c.blocks.size then some ⟨⟨.running (jump f block), []⟩, .assert hf hv hb⟩ else none
    else none
  | some (.term (.malloc op dest block)) =>
    match hv : operand f op with
    | some (.u64 bytes) => match hh : mallocHeap f.heap bytes with
      | none => none
      | some heap => match hw : write c {f with heap := heap} dest (.pointer f.heap.size 0) with
        | none => none
        | some target => if hb : block < c.blocks.size then
            some ⟨⟨.running (jump target block), [.alloc f.heap.size bytes]⟩, .malloc hf hv hh hw hb⟩ else none
    | _ => none
  | some (.term (.free op dest block)) =>
    match hv : operand f op with
    | some (.pointer object index) => match hh : freeHeap f.heap object index with
      | none => none
      | some heap => match hw : write c {f with heap := heap} dest .unit with
        | none => none
        | some target => if hb : block < c.blocks.size then
            some ⟨⟨.running (jump target block), [.free object]⟩, .free hf hv hh hw hb⟩ else none
    | _ => none
  | some (.term .ret) =>
    match hv : (f.locals[(0 : Nat)]?).join with
    | some (.i64 v) => some ⟨⟨.returned v f, []⟩, .ret hf hv⟩
    | _ => none

def tick (c : Code) (f : Frame) : Option Next := (next c f).map Subtype.val

theorem tick_sound (h : tick c f = some result) : Step c (.running f) result.events result.machine := by
  unfold tick at h
  cases hn : next c f with
  | none => simp [hn] at h
  | some certified => simp [hn] at h; subst result; exact certified.property

theorem Step.deterministic (a : Step c m es n) (b : Step c m fs p) : es = fs ∧ n = p := by
  cases a <;> cases b <;> simp_all

inductive Steps (c : Code) : Machine → List Event → Machine → Prop where
  | nil : Steps c m [] m
  | cons : Step c m first mid → Steps c mid rest finish → Steps c m (first ++ rest) finish

theorem returned_no_step {target : Machine} : ¬ Step c (.returned v f) es target := by intro h; cases h

theorem Steps.returned_only (h : Steps c (.returned v f) es m) : es = [] ∧ m = .returned v f := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons first _ => cases first

theorem Steps.returned_deterministic (a : Steps c m es (.returned v f)) (b : Steps c m fs (.returned w g)) :
    v = w ∧ f = g ∧ es = fs := by
  generalize he : Machine.returned v f = finish at a
  induction a generalizing v f w g fs with
  | nil => cases he; obtain ⟨rfl, eq⟩ := b.returned_only; cases eq; exact ⟨rfl, rfl, rfl⟩
  | cons first tail ih => cases b with
    | nil => cases first
    | cons other rest =>
      obtain ⟨rfl, rfl⟩ := first.deterministic other
      obtain ⟨rfl, rfl, rfl⟩ := ih rest he
      exact ⟨rfl, rfl, rfl⟩

/-- One unit of fuel per statement or terminator, including Return. -/
def execute : Nat → Code → Frame → Option Outcome
  | 0, _, _ => none
  | fuel + 1, c, f => do
    let n ← tick c f
    match n.machine with
    | .returned value frame => pure ⟨value, frame, n.events⟩
    | .running frame =>
      let out ← execute fuel c frame
      pure { out with events := n.events ++ out.events }

theorem execute_sound (h : execute fuel c f = some out) :
    Steps c (.running f) out.events (.returned out.value out.frame) := by
  induction fuel generalizing f out with
  | zero => simp [execute] at h
  | succ fuel ih =>
    cases hn : tick c f with
    | none => simp [execute, hn] at h
    | some n =>
      have step := tick_sound hn
      cases hm : n.machine with
      | returned value frame =>
        simp [execute, hn, hm] at h
        subst out
        simpa using Steps.cons (hm ▸ step) Steps.nil
      | running frame =>
        cases hr : execute fuel c frame with
        | none => simp [execute, hn, hm, hr] at h
        | some result =>
          simp [execute, hn, hm, hr] at h
          subst out
          exact .cons (hm ▸ step) (ih hr)

theorem execute_unique (h : execute fuel c f = some out)
    (run : Steps c (.running f) events (.returned value frame)) :
    value = out.value ∧ frame = out.frame ∧ events = out.events := by
  obtain ⟨rfl, rfl, rfl⟩ := (execute_sound h).returned_deterministic run
  exact ⟨rfl, rfl, rfl⟩

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

theorem tick_complete (step : Step c (.running f) events target) :
    tick c f = some ⟨target, events⟩ := by
  rw [tick_eq_rawTick]
  cases step <;> simp_all [rawTick]

def initial (c : Code) : Frame := ⟨0, 0, Array.replicate c.locals.size none, #[]⟩
def heapEmpty (f : Frame) : Bool := f.heap.all (fun obj => !obj.alive)

end Jihoo.ReferenceCfg
