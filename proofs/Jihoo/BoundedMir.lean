import Jihoo.HeapLifecycle

/-! A bounded closed MIR CFG interpreter. The vocabulary follows the retained
MIR constructors, not a source macro trace. Allocation succeeds with fresh abstract
objects, initially uninitialized cells. Address casts expose only a nonnull tag;
raw addresses, allocator failure and arbitrary MIR are outside this model. -/
namespace Jihoo.BoundedMir

abbrev Event := HeapLifecycle.Event

def wordBound : Nat := 2^64
def scalarBound : Nat := 2^63

inductive Ty where
  | i64 | u64 | bool | ptr | unit
  deriving DecidableEq, Repr
inductive Value where
  | i64 (n : Nat) | u64 (n : Nat) | boolean (b : Bool)
  | pointer (object index : Nat)
  | address (object : Nat)
  | unit
  deriving DecidableEq, Repr
inductive Constant where
  | i64 (n : Nat) | u64 (n : Nat) | boolean (b : Bool) | unit
  deriving DecidableEq, Repr
structure Place where
  slot : Nat
  deref : Bool
  deriving DecidableEq, Repr
inductive Operand where
  | copy (place : Place)
  | constant (value : Constant)
  deriving DecidableEq, Repr
inductive Bin where
  | add | mul | lt | ne
  deriving DecidableEq, Repr
inductive Rvalue where
  | use (operand : Operand)
  | bin (op : Bin) (left right : Operand)
  | ptrCast (operand : Operand)
  | offset (pointer index : Operand)
  deriving DecidableEq, Repr
structure Stmt where
  place : Place
  value : Rvalue
  deriving DecidableEq, Repr
inductive Term where
  | goto (block : Nat)
  | switch (value : Operand) (cases : List (Nat × Nat)) (otherwise : Nat)
  | assert (condition : Operand) (next : Nat)
  | malloc (bytes : Operand) (destination : Place) (next : Nat)
  | free (pointer : Operand) (destination : Place) (next : Nat)
  | ret
  deriving DecidableEq, Repr
structure Block where
  statements : Array Stmt
  term : Term
  deriving DecidableEq, Repr
structure Code where
  locals : Array Ty
  blocks : Array Block
  deriving DecidableEq, Repr
structure Object where
  alive : Bool
  cells : Array (Option Nat)
  deriving DecidableEq, Repr
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
  | .pointer _ _ => .ptr | .unit => .unit

def constant : Constant → Option Value
  | .i64 n => if n < scalarBound then some (.i64 n) else none
  | .u64 n => if n < wordBound then some (.u64 n) else none
  | .boolean b => some (.boolean b)
  | .unit => some .unit

def load (heap : Array Object) (object index : Nat) : Option Nat := do
  let obj ← heap[object]?
  if !obj.alive then none else (obj.cells[index]?).join

def operand (f : Frame) : Operand → Option Value
  | .constant c => constant c
  | .copy place => do
    let v ← (f.locals[place.slot]?).join
    if place.deref then
      let .pointer object index := v | none
      return .i64 (← load f.heap object index)
    else pure v

def binary : Bin → Value → Value → Option Value
  | .add, .u64 a, .u64 b => if a + b < wordBound then some (.u64 (a + b)) else none
  | .mul, .u64 a, .u64 b => if a * b < wordBound then some (.u64 (a * b)) else none
  | .lt, .u64 a, .u64 b => some (.boolean (a < b))
  | .ne, .u64 a, .u64 b => some (.boolean (a != b))
  | .ne, .address _, .u64 0 | .ne, .u64 0, .address _ => some (.boolean true)
  | _, _, _ => none

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

def write (c : Code) (f : Frame) (place : Place) (v : Value) : Option Frame := do
  let ty ← c.locals[place.slot]?
  if place.deref then
    if ty != .ptr then none else do
    let .pointer object index ← (f.locals[place.slot]?).join | none
    let .i64 payload := v | none
    let obj ← f.heap[object]?
    if obj.alive && index < obj.cells.size && payload < scalarBound then
      pure { f with heap := f.heap.set! object { obj with cells := obj.cells.set! index (some payload) } }
    else none
  else if valueType v == ty && place.slot < f.locals.size then
    pure { f with locals := f.locals.set! place.slot (some v) }
  else none

/-- Malloc creates raw cells, not the already-initialized source buffer. -/
def mallocHeap (heap : Array Object) (bytes : Nat) : Option (Array Object) :=
  if 0 < bytes && bytes % 8 == 0 && bytes ≤ 32768 && heap.size < 512 &&
      (heap.toList.map (fun obj => obj.cells.size)).sum + bytes / 8 ≤ 4096 then
    some (heap.push ⟨true, Array.replicate (bytes / 8) none⟩)
  else none

def freeHeap (heap : Array Object) (object index : Nat) : Option (Array Object) := do
  let obj ← heap[object]?
  if obj.alive && index == 0 then some (heap.set! object { obj with alive := false }) else none

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

def placeValid (c : Code) (p : Place) : Bool :=
  p.slot < c.locals.size && (!p.deref || c.locals[p.slot]? == some .ptr)
def operandValid (c : Code) : Operand → Bool
  | .copy p => placeValid c p
  | .constant value => (constant value).isSome
def operandType (c : Code) : Operand → Option Ty
  | .constant (.i64 _) => some .i64
  | .constant (.u64 _) => some .u64
  | .constant (.boolean _) => some .bool
  | .constant .unit => some .unit
  | .copy p => if p.deref then
      if c.locals[p.slot]? == some .ptr then some .i64 else none
    else c.locals[p.slot]?

def destinationType (c : Code) (p : Place) : Option Ty :=
  if p.deref then if c.locals[p.slot]? == some .ptr then some .i64 else none
  else c.locals[p.slot]?

def rvalueType (c : Code) : Rvalue → Option Ty
  | .use a => operandType c a
  | .bin op a b =>
    if operandType c a == some .u64 && operandType c b == some .u64 then
      some (match op with | .add | .mul => .u64 | .lt | .ne => .bool)
    else none
  | .ptrCast a => if operandType c a == some .ptr then some .u64 else none
  | .offset a b => if operandType c a == some .ptr && operandType c b == some .u64 then some .ptr else none

def rvalueValid (c : Code) (r : Rvalue) : Bool :=
  (rvalueType c r).isSome && match r with
  | .use a | .ptrCast a => operandValid c a
  | .bin _ a b | .offset a b => operandValid c a && operandValid c b

def stmtValid (c : Code) (s : Stmt) : Bool :=
  placeValid c s.place && rvalueValid c s.value && destinationType c s.place == rvalueType c s.value

def termValid (c : Code) : Term → Bool
  | .goto b => b < c.blocks.size
  | .switch op cases otherwise => operandValid c op &&
      ([some Ty.bool, some Ty.u64, some Ty.i64].contains (operandType c op)) && otherwise < c.blocks.size &&
      cases.length ≤ 512 && decide (cases.map Prod.fst).Nodup &&
      cases.all (fun pair => pair.1 < wordBound && pair.2 < c.blocks.size)
  | .assert op next => operandValid c op && operandType c op == some .bool && next < c.blocks.size
  | .malloc op dest next => operandValid c op && operandType c op == some .u64 &&
      !dest.deref && c.locals[dest.slot]? == some .ptr && next < c.blocks.size
  | .free op dest next => operandValid c op && operandType c op == some .ptr &&
      !dest.deref && c.locals[dest.slot]? == some .unit && next < c.blocks.size
  | .ret => true

/-- Scan every row, including unreachable blocks; unknown constructors cannot
be represented and the external decoder rejects them rather than dropping them. -/
def valid (c : Code) : Bool :=
  c.locals.size ≤ 512 && c.locals[0]? == some .i64 && 0 < c.blocks.size && c.blocks.size ≤ 512 &&
  (c.blocks.toList.map (fun b => b.statements.size)).sum ≤ 4096 &&
  c.blocks.all (fun b => b.statements.all (stmtValid c) && termValid c b.term)

def initial (c : Code) : Frame := ⟨0, 0, Array.replicate c.locals.size none, #[]⟩
def heapEmpty (f : Frame) : Bool := f.heap.all (fun obj => !obj.alive)

structure Accepted (c : Code) where
  fuel : Nat
  fuel_bound : fuel ≤ 10000
  valid_code : valid c = true
  outcome : Outcome
  execution : execute fuel c (initial c) = some outcome
  no_live_heap : heapEmpty outcome.frame = true

def admit (c : Code) (fuel : Nat) : Option (Accepted c) :=
  if hb : fuel ≤ 10000 then
  if hv : valid c = true then
    match he : execute fuel c (initial c) with
    | none => none
    | some out => if hh : heapEmpty out.frame = true then some ⟨fuel, hb, hv, out, he, hh⟩ else none
  else none else none

theorem accepted_execution (a : Accepted c) :
    Steps c (.running (initial c)) a.outcome.events (.returned a.outcome.value a.outcome.frame) := execute_sound a.execution

theorem accepted_all_returns (a : Accepted c)
    (run : Steps c (.running (initial c)) events (.returned value frame)) :
    value = a.outcome.value ∧ frame = a.outcome.frame ∧ events = a.outcome.events := execute_unique a.execution run

theorem accepted_all_return_heaps (a : Accepted c)
    (run : Steps c (.running (initial c)) events (.returned value frame)) : heapEmpty frame = true := by
  obtain ⟨_, rfl, _⟩ := accepted_all_returns a run
  exact a.no_live_heap

end Jihoo.BoundedMir
